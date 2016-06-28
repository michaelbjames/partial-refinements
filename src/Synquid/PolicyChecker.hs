-- | Type-checker for programs without holes that collects errors
module Synquid.PolicyChecker (localize, repair) where

import Synquid.Logic
import Synquid.Type
import Synquid.Program
import Synquid.Error
import Synquid.SolverMonad
import Synquid.TypeConstraintSolver hiding (freshId, freshVar)
import Synquid.Explorer
import Synquid.TypeChecker
import Synquid.Util
import Synquid.Pretty
import Synquid.Resolver
import Synquid.Tokens

import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Foldable as F
import Control.Monad.Logic
import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative hiding (empty)
import Control.Lens

import Debug.Trace

-- | 'localize' @eParams tParams goal@ : reconstruct intermediate type annotations in @goal@
-- and return the resulting program in ANF together with a list of type-violating bindings
localize :: MonadHorn s => Bool -> ExplorerParams -> TypingParams -> Goal -> s (Either ErrorMessage (RProgram, Requirements))
localize isRecheck eParams tParams goal = do
    initTS <- initTypingState $ gEnvironment goal
    runExplorer (eParams { _sourcePos = gSourcePos goal }) tParams initTS go
  where
    go = do
      aImpl <- aNormalForm "T" (gImpl goal)
      writeLog 2 (pretty aImpl)      
      
      p <- localizeTopLevel goal { gImpl = aImpl }
      labels <- runInSolver getViolatingLabels
      reqs <- uses requiredTypes (restrictDomain labels) >>= (mapM (liftM nub . mapM (runInSolver . finalizeType)))
      finalP <- runInSolver $ finalizeProgram p
      if isRecheck
        then if Map.null reqs
              then return (finalP, Map.empty)
              else throwErrorWithDescription $ (nest 2 (text "Repair failed with violations:" $+$ vMapDoc text pretty reqs)) $+$ text "when checking" $+$ pretty p
        else return (finalP, reqs)
      
repair :: MonadHorn s => ExplorerParams -> TypingParams -> Environment -> RProgram -> Requirements -> s (Either ErrorMessage RProgram)
repair eParams tParams env p violations = do
    initTS <- initTypingState env
    runExplorer eParams tParams initTS go
  where
    go = do
      writeLog 1 $ (nest 2 (text "Violated requirements:" $+$ vMapDoc text pretty violations)) $+$ text "when checking" $+$ pretty p
      requiredTypes .= violations
      replaceViolations env p
      
{- Localization -}
    
localizeTopLevel :: MonadHorn s => Goal -> Explorer s RProgram
localizeTopLevel (Goal funName env (ForallT a sch) impl depth pos) = localizeTopLevel (Goal funName (addTypeVar a env) sch impl depth pos)
localizeTopLevel (Goal funName env (ForallP sig sch) impl depth pos) = localizeTopLevel (Goal funName (addBoundPredicate sig env) sch impl depth pos)
localizeTopLevel (Goal funName env (Monotype typ@(FunctionT _ _ _)) impl depth _) = do
  let typ' = renameAsImpl (isBound env) impl typ
  recCalls <- runInSolver (currentAssignment typ') >>= recursiveCalls
  polymorphic <- asks $ _polyRecursion . fst
  predPolymorphic <- asks $ _predPolyRecursion . fst
  let tvs = env ^. boundTypeVars
  let pvs = env ^. boundPredicates      
  let predGeneralized sch = if predPolymorphic then foldr ForallP sch pvs else sch -- Version of @t'@ generalized in bound predicate variables of the enclosing function          
  let typeGeneralized sch = if polymorphic then foldr ForallT sch tvs else sch -- Version of @t'@ generalized in bound type variables of the enclosing function
  
  let env' = foldr (\(f, t) -> addPolyVariable f (typeGeneralized . predGeneralized . Monotype $ t) . (shapeConstraints %~ Map.insert f (shape typ'))) env recCalls
  let ctx = \p -> if null recCalls then p else Program (PFix (map fst recCalls) p) typ'
  p <- inContext ctx  $ localizeI env' typ' impl
  return $ ctx p

  where
    -- | 'recursiveCalls' @t@: name-type pairs for recursive calls to a function with type @t@ (0 or 1)
    recursiveCalls t = do
      fixStrategy <- asks $ _fixStrategy . fst
      case fixStrategy of
        AllArguments -> do recType <- fst <$> recursiveTypeTuple t ffalse; if recType == t then return [] else return [(funName, recType)]
        FirstArgument -> do recType <- recursiveTypeFirst t; if recType == t then return [] else return [(funName, recType)]
        DisableFixpoint -> return []
        Nonterminating -> return [(funName, t)]

    -- | 'recursiveTypeTuple' @t fml@: type of the recursive call to a function of type @t@ when a lexicographic tuple of all recursible arguments decreases;
    -- @fml@ denotes the disjunction @x1' < x1 || ... || xk' < xk@ of strict termination conditions on all previously seen recursible arguments to be added to the type of the last recursible argument;
    -- the function returns a tuple of the weakend type @t@ and a flag that indicates if the last recursible argument has already been encountered and modified
    recursiveTypeTuple (FunctionT x tArg tRes) fml = do
      case terminationRefinement x tArg of
        Nothing -> do
          (tRes', seenLast) <- recursiveTypeTuple tRes fml
          return (FunctionT x tArg tRes', seenLast)
        Just (argLt, argLe) -> do
          y <- freshVar env "x"
          let yForVal = Map.singleton valueVarName (Var (toSort $ baseTypeOf tArg) y)
          (tRes', seenLast) <- recursiveTypeTuple (renameVar (isBound env) x y tArg tRes) (fml `orClean` substitute yForVal argLt)
          if seenLast
            then return (FunctionT y (addRefinement tArg argLe) tRes', True) -- already encountered the last recursible argument: add a nonstrict termination refinement to the current one
            -- else return (FunctionT y (addRefinement tArg (fml `orClean` argLt)) tRes', True) -- this is the last recursible argument: add the disjunction of strict termination refinements
            else if fml == ffalse
                  then return (FunctionT y (addRefinement tArg argLt) tRes', True)
                  else return (FunctionT y (addRefinement tArg (argLe `andClean` (fml `orClean` argLt))) tRes', True) -- TODO: this version in incomplete (does not allow later tuple values to go up), but is much faster
    recursiveTypeTuple t _ = return (t, False)

    -- | 'recursiveTypeFirst' @t fml@: type of the recursive call to a function of type @t@ when only the first recursible argument decreases
    recursiveTypeFirst (FunctionT x tArg tRes) = do
      case terminationRefinement x tArg of
        Nothing -> FunctionT x tArg <$> recursiveTypeFirst tRes
        Just (argLt, _) -> do
          y <- freshVar env "x"
          return $ FunctionT y (addRefinement tArg argLt) (renameVar (isBound env) x y tArg tRes)
    recursiveTypeFirst t = return t

    -- | If argument is recursible, return its strict and non-strict termination refinements, otherwise @Nothing@
    terminationRefinement argName (ScalarT IntT fml) = Just ( valInt |>=| IntLit 0  |&|  valInt |<| intVar argName,
                                                              valInt |>=| IntLit 0  |&|  valInt |<=| intVar argName)
    terminationRefinement argName (ScalarT dt@(DatatypeT name _ _) fml) = case env ^. datatypes . to (Map.! name) . wfMetric of
      Nothing -> Nothing
      Just mName -> let 
                      metric x = Pred IntS mName [x]
                      argSort = toSort dt
                    in Just ( metric (Var argSort valueVarName) |>=| IntLit 0  |&| metric (Var argSort valueVarName) |<| metric (Var argSort argName),
                              metric (Var argSort valueVarName) |>=| IntLit 0  |&| metric (Var argSort valueVarName) |<=| metric (Var argSort argName))
    terminationRefinement _ _ = Nothing

localizeTopLevel (Goal _ env (Monotype t) impl depth _) = localizeI env t impl

-- | 'localizeI' @env t impl@ :: reconstruct unknown types and terms in a judgment @env@ |- @impl@ :: @t@ where @impl@ is a (possibly) introduction term
-- (top-down phase of bidirectional reconstruction)
localizeI :: MonadHorn s => Environment -> RType -> UProgram -> Explorer s RProgram
localizeI env t (Program p AnyT) = localizeI' env t p

localizeI' env t PErr = generateError env
localizeI' env t PHole = error "Holes not supported when checking policies"
localizeI' env t (PLet x iDef@(Program (PFun _ _) _) iBody) = do -- lambda-let: remember and type-check on use
  lambdaLets %= Map.insert x (env, iDef)
  pBody <- inContext (\p -> Program (PLet x uHole p) t) $ localizeI env t iBody
  (_, pDef) <- uses lambdaLets (Map.! x)
  return $ Program (PLet x pDef pBody) t
localizeI' env t@(FunctionT _ tArg tRes) impl = case impl of 
  PFix _ impl -> localizeI env t impl
  PFun y impl -> do
    let ctx = \p -> Program (PFun y p) t
    pBody <- inContext ctx $ localizeI (unfoldAllVariables $ addVariable y tArg $ env) tRes impl
    return $ ctx pBody
  PSymbol f -> localizeETopLevel env t (untyped impl)
  _ -> throwErrorWithDescription $ text "Cannot assign function type" </> squotes (pretty t) </>
                    text "to non-lambda term" </> squotes (pretty $ untyped impl)
localizeI' env t@(ScalarT _ _) impl = case impl of
  PFun _ _ -> throwErrorWithDescription $ text "Cannot assign non-function type" </> squotes (pretty t) </>
                           text "to lambda term" </> squotes (pretty $ untyped impl)
                           
  PLet x iDef iBody -> do -- E-term let (since lambda-let was considered before)
    pDef <- inContext (\p -> Program (PLet x p (Program PHole t)) t) $ localizeETopLevel env AnyT iDef
    pBody <- inContext (\p -> Program (PLet x pDef p) t) $ localizeI (addLetBound x (typeOf pDef) env) t iBody
    return $ Program (PLet x pDef pBody) t
    
  PIf iCond iThen iElse -> do
    pCond <- inContext (\p -> Program (PIf p (Program PHole t) (Program PHole t)) t) $ localizeETopLevel env (ScalarT BoolT ftrue) iCond
    let ScalarT BoolT cond = typeOf pCond
    pThen <- inContext (\p -> Program (PIf pCond p (Program PHole t)) t) $ localizeI (addAssumption (substitute (Map.singleton valueVarName ftrue) cond) env) t iThen
    pElse <- inContext (\p -> Program (PIf pCond pThen p) t) $ localizeI (addAssumption (substitute (Map.singleton valueVarName ffalse) cond) env) t iElse
    return $ Program (PIf pCond pThen pElse) t
    
  PMatch iScr iCases -> do
    (consNames, consTypes) <- unzip <$> checkCases Nothing iCases
    let scrT = refineTop env $ shape $ lastType $ head consTypes
    
    pScrutinee <- inContext (\p -> Program (PMatch p []) t) $ localizeETopLevel env scrT iScr            
    pCases <- zipWithM (localizeCase env pScrutinee t) iCases consTypes    
    return $ Program (PMatch pScrutinee pCases) t
      
  _ -> localizeETopLevel env t (untyped impl)
  
  where
    -- Check that all constructors are known and belong to the same datatype
    checkCases mName (Case consName args _ : cs) = case Map.lookup consName (allSymbols env) of
      Nothing -> throwErrorWithDescription $ text "Not in scope: data constructor" </> squotes (text consName)
      Just consSch -> do
                        consT <- instantiate env consSch True args -- Set argument names in constructor type to user-provided binders
                        case lastType consT of
                          (ScalarT (DatatypeT dtName _ _) _) -> do
                            case mName of
                              Nothing -> return ()                            
                              Just name -> if dtName == name
                                             then return ()
                                             else throwErrorWithDescription $ text "Expected constructor of datatype" </> squotes (text name) </> 
                                                               text "and got constructor" </> squotes (text consName) </> 
                                                               text "of datatype" </> squotes (text dtName)
                            if arity (toMonotype consSch) /= length args 
                              then throwErrorWithDescription $ text "Constructor" </> squotes (text consName)
                                            </> text "expected" </> pretty (arity (toMonotype consSch)) </> text "binder(s) and got" <+> pretty (length args)
                              else ((consName, consT) :) <$> checkCases (Just dtName) cs
                          _ -> throwErrorWithDescription $ text "Not in scope: data constructor" </> squotes (text consName)
    checkCases _ [] = return []
  
localizeCase env pScrutinee@(Program (PSymbol x) scrT) t (Case consName args iBody) consT = cut $ do  
  runInSolver $ matchConsType (lastType consT) (typeOf pScrutinee)
  consT' <- runInSolver $ currentAssignment consT
  (syms, ass) <- caseSymbols env (Var (toSort $ baseTypeOf scrT) x) args consT'
  let caseEnv = foldr (uncurry addVariable) (addAssumption ass env) syms
  pCaseExpr <- inContext (\p -> Program (PMatch pScrutinee [Case consName args p]) t) $ 
               localizeI caseEnv t iBody
  return $ Case consName args pCaseExpr  

-- | 'localizeE' @env t impl@ :: reconstruct unknown types and terms in a judgment @env@ |- @impl@ :: @t@ where @impl@ is an elimination term
-- (bottom-up phase of bidirectional reconstruction)    
localizeETopLevel :: MonadHorn s => Environment -> RType -> UProgram -> Explorer s RProgram
localizeETopLevel env t impl = do
  (Program pTerm pTyp) <- localizeE env t impl  
  pTyp' <- runInSolver $ currentAssignment pTyp
  return $ Program pTerm pTyp'

localizeE :: MonadHorn s => Environment -> RType -> UProgram -> Explorer s RProgram
localizeE env t (Program p AnyT) = localizeE' env t p

localizeE' env typ PHole = error "Holes not supported when checking policies"
localizeE' env typ (PSymbol name) = case lookupSymbol name (arity typ) env of
  Nothing -> throwErrorWithDescription $ text "Not in scope:" </> text name
  Just sch -> do
    t <- symbolType env name sch
    let p = Program (PSymbol name) t
    case Map.lookup name (env ^. shapeConstraints) of
      Nothing -> return ()
      Just sc -> addConstraint $ Subtype env (refineBot env $ shape t) (refineTop env sc) False ""
    when (not $ hasAny typ) $ checkSymbol env typ p
    return p
localizeE' env typ (PApp iFun iArg) = do
  x <- freshVar env "x"
  pFun <- inContext (\p -> Program (PApp p uHole) typ) $ localizeE env (FunctionT x AnyT typ) iFun
  let FunctionT x tArg tRes = typeOf pFun
  let argCtx = \p -> Program (PApp pFun p) tRes
  if isFunctionType tArg
  then do -- Higher-order argument: its value is not required for the function type, enqueue an auxiliary goal
    pArg <- generateHOArg env argCtx tArg iArg
    return $ argCtx pArg
  else do -- First-order argument: generate now
    pArg@(Program (PSymbol y) t) <- inContext argCtx $ localizeE env tArg iArg
    return $ Program (PApp pFun pArg) (substituteInType (isBound env) (Map.singleton x (Var (toSort $ baseTypeOf t) y)) tRes)
  where
    generateHOArg env ctx tArg iArg = case content iArg of
      PSymbol f -> do
        lets <- use lambdaLets
        case Map.lookup f lets of
          Nothing -> -- This is a function from the environment, with a known type: check symbol against tArg                      
            localizeETopLevel env tArg iArg 
          Just (env', def) -> do -- This is a locally defined function: check it against tArg as a fixpoint
            lambdaLets %= Map.delete f -- Remove from lambda-lets in case of recursive call
            writeLog 1 $ text "Checking lambda-let argument" <+> pretty iArg <+> text "::" <+> pretty tArg <+> text "in" $+$ pretty (ctx (untyped PHole))
            def' <- inContext ctx $ localizeTopLevel (Goal f env' (Monotype tArg) def 0 noPos)
            lambdaLets %= Map.insert f (env', def')
            return iArg
      _ -> do -- Lambda-abstraction: check against tArg
            let tArg' = renameAsImpl (isBound env) iArg tArg
            writeLog 1 $ text "Checking lambda argument" <+> pretty iArg <+> text "::" <+> pretty tArg' <+> text "in" $+$ pretty (ctx (untyped PHole))
            inContext ctx $ localizeI env tArg' iArg
      
localizeE' env typ impl = do
  throwErrorWithDescription $ text "Expected application term of type" </> squotes (pretty typ) </>
                                          text "and got" </> squotes (pretty $ untyped impl)
                                          
checkSymbol :: MonadHorn s => Environment -> RType -> RProgram -> Explorer s ()
checkSymbol env typ p@(Program (PSymbol name) pTyp) = do
  ctx <- asks $ _context . fst
  writeLog 1 $ text "Checking" <+> pretty p <+> text "::" <+> pretty typ <+> text "in" $+$ pretty (ctx (untyped PHole))
  
  requiredTypes %= Map.insertWith (++) name [typ]
  addConstraint $ Subtype env pTyp typ False name
  runInSolver simplifyAllConstraints
  
{- Repair -}

replaceViolations :: MonadHorn s => Environment -> RProgram -> Explorer s RProgram
replaceViolations env (Program (PFun x body) t@(FunctionT _ tArg _)) = do
  body' <- replaceViolations (addVariable x tArg env) body
  return $ Program (PFun x body') t
replaceViolations env (Program (PIf cond thn els) t) = do
  let ScalarT BoolT fml = typeOf cond
  thn' <- replaceViolations (addAssumption (substitute (Map.singleton valueVarName ftrue) fml) env) thn
  els' <- replaceViolations (addAssumption (substitute (Map.singleton valueVarName ffalse) fml) env) els
  return $ Program (PIf cond thn' els') t
replaceViolations env (Program (PMatch scr cases) t) = error "replaceViolations: matches not implemented"
  -- do
  -- cases' <- mapM reaplceInCase cases
  -- return $ Program (PMatch scr cases') t
  -- where
    -- reaplceInCase (Case consName args iBody) = do  
      -- runInSolver $ matchConsType (lastType consT) (typeOf pScrutinee)
      -- consT' <- runInSolver $ currentAssignment consT
      -- (syms, ass) <- caseSymbols env (Var (toSort $ baseTypeOf scrT) x) args consT'
  -- let caseEnv = foldr (uncurry addVariable) (addAssumption ass env) syms
  -- pCaseExpr <- inContext (\p -> Program (PMatch pScrutinee [Case consName args p]) t) $ 
               -- localizeI caseEnv t iBody
  -- return $ Case consName args pCaseExpr  
replaceViolations env (Program (PFix xs body) t) = do
  body' <- replaceViolations env body
  return $ Program (PFix xs body') t
replaceViolations env (Program (PLet x def body) t) = do
  reqs <- use requiredTypes
  (newDefs, def') <- case Map.lookup x reqs of
            Nothing -> do
                          def'<- replaceViolations env def
                          return ([], def')
            Just ts -> generateRepair env (head ts) def -- ToDo: other ts
  body' <- replaceViolations (addLetBound x (typeOf def') env) body
  return $ foldDefs (newDefs ++ [(x, def')]) body' t
replaceViolations env (Program (PApp fun arg) t) = do
  fun' <- replaceViolations env fun
  arg' <- replaceViolations env arg
  return $ Program (PApp fun' arg') t
replaceViolations _ p = return p

generateRepair :: MonadHorn s => Environment -> RType -> RProgram -> Explorer s ([(Id, RProgram)], RProgram)
generateRepair env typ p = do
  writeLog 1 $ text "Generating repair for" <+> pretty p <+> text "::" <+> pretty typ
  cUnknown <- Unknown Map.empty <$> freshId "C"
  addConstraint $ WellFormedCond env cUnknown
  addConstraint $ Subtype (addAssumption cUnknown env) (typeOf p) typ False ""
  pElse <- defaultValue
  ifte (runInSolver $ solveTypeConstraints)
    (const $ do -- Condition found
      cond <- conjunction <$> currentValuation cUnknown -- Todo: multiple valuations: disjunction
      (cDefs, cBody) <- generateCondition cond      
      mkCheck cDefs cBody p pElse)
    (return ([], pElse)) -- No condition found, Todo: issue a warning
  where
    targetPolicy = case typ of
      ScalarT (DatatypeT _ _ [fml]) _ -> fml
      _ -> error $ unwords ["generateRepair: ill-formed target type", show typ]
  
    -- | Public version of @p@
    defaultValue = do
      let f = head $ symbolList p
      let f' = defaultPrefix ++ drop 3 f -- ToDo: better way of finding default value
      case lookupSymbol f' 0 env of
        Nothing -> throwErrorWithDescription $ text "No default value found for sensitive component" $+$ text f
        Just (Monotype t) -> return $ Program (PSymbol f') t
        
    -- | Synthesize a tagged Boolean program with value equivalent to @fml@ and policy (@targetPolicy@ && @fml@)
    generateCondition fml = do
      let strippedEnv = over symbols (Map.map (Map.foldlWithKey (updateSymbol fml) Map.empty)) env
      pureCond <- generatePureCondition strippedEnv fml
      liftCondition env strippedEnv (targetPolicy |&| fml) pureCond      
        
    -- | Synthesize a Boolean program equivalent to @fml@ put of components stripped of their tags
    generatePureCondition strippedEnv fml = do
      let allConjuncts = Set.toList $ conjunctsOf fml
      conjuncts <- mapM (genPureConjunct strippedEnv) allConjuncts
      let andSymb = Program (PSymbol $ binOpTokens Map.! And) (toMonotype $ binOpType And)
      let conjoin p1 p2 = Program (PApp (Program (PApp andSymb p1) boolAll) p2) boolAll
      let pCond = foldl1 conjoin conjuncts
      aCond <- aNormalForm "TT" pCond
      -- reconstructI strippedEnv (ScalarT BoolT $ valBool |<=>| fml) (eraseTypes aCond) -- re-check ANF to get rid of ghosts
      return aCond
      
    genPureConjunct strippedEnv c = do
      let targetType = ScalarT BoolT $ valBool |<=>| c
      local (over (_2 . condQualsGen) (const (\_ _ -> emptyQSpace))) $ cut (reconstructE strippedEnv targetType)
      
    updateSymbol :: Formula -> Map Id RSchema -> Id -> RSchema -> Map Id RSchema
    updateSymbol _ m name _ | -- This is a default value: remove
      take (length defaultPrefix) name == defaultPrefix   = m
    updateSymbol targetRefinement m name (Monotype t) = 
      let 
        t' = stripTags t 
        symbolPreds = predsOfType t'
        targetPreds = predsOf targetRefinement
      in if t /= t' && disjoint symbolPreds targetPreds 
          -- trace (unwords ["updateSymbol: ignoring", name, "with symbol preds", show symbolPreds, "and target preds", show targetPreds]) $
          then m -- This is a stripped component whose type has no predicates in common with our target: exclude it form the environment
          else Map.insert name (Monotype t') m
    updateSymbol _ m name sch | -- This is a function from base tagged library: remove
      isTagged (lastType $ toMonotype sch)                = m                  
    updateSymbol _ m name sch = Map.insert name sch m
      
    defaultPrefix = "default"
    
    isTagged (ScalarT (DatatypeT dtName _ _) _) | dtName == "Tagged" = True
    isTagged t = False
    
    stripTags t@(ScalarT (DatatypeT dtName [dtArg] _) _) 
      | isTagged t   = dtArg    
    stripTags (FunctionT x tArg tRes) = FunctionT x tArg (stripTags tRes)
    stripTags t = t
    
    -- | 'liftCondition' @env strippedEnv policy p@: turn a pure E-term @p@ into a tagged one, 
    -- by binding all lets that have different types in @env@ and @strippedEnv@
    liftCondition env strippedEnv policy (Program (PLet x def body) typ) = do
      let arity = length (symbolList def) - 1
      let headSymbol = head $ symbolList def
      let realType = case lookupSymbol headSymbol arity env of
                    Nothing -> error $ unwords ["liftCondition: cannot find", headSymbol, "in original environment"]
                    Just t -> t
      let strippedType = case lookupSymbol headSymbol arity strippedEnv of
                        Nothing -> error $ unwords ["liftCondition: cannot find", headSymbol, "in stripped environment"]
                        Just t -> t
      let addX = addLetBound x (typeOf def)
      (defs', body') <- liftCondition (addX env) (addX strippedEnv) policy body
      if realType == strippedType
        then return ((x, def):defs', body') -- This definition hasn't been stripped: leave as is
        else do -- This definition has been stripped: turn into a bind
          tmp <- freshId "TT"
          return ([(tmp, def)], mkBind tmp x (foldDefs defs' body' (typeOf body')))
    liftCondition env strippedEnv policy pCond = do
      tmp <- freshId "TT"
      return ([(tmp, mkReturn pCond)], untyped $ PSymbol tmp)

    mkTagged a policy = DatatypeT "Tagged" [a] [policy]
    
    mkBind argName x body = 
      let 
        app = untyped (PApp (untyped (PSymbol "bind")) (untyped (PSymbol argName)))
        fun = untyped (PFun x body)
      in untyped (PApp app fun)
      
    mkReturn p = untyped (PApp (untyped (PSymbol "return")) p)
    
    mkCheck cDefs cBody pThen pElse = do
      cTmp <- freshId "TT"
      pTmp <- freshId "TT"
      let allDefs = cDefs ++ [(cTmp, cBody), (pTmp, pThen)]
      let app1 = untyped (PApp (untyped (PSymbol "if_")) (untyped (PSymbol cTmp)))
      let app2 = untyped (PApp app1 (untyped (PSymbol pTmp)))
      return (allDefs, untyped (PApp app2 pElse))

{- Misc -}  
                                            
-- | 'aNormalForm' @p@: program equivalent to @p@ where arguments and top-level e-terms do not contain applications
aNormalForm :: MonadHorn s => Id -> RProgram -> Explorer s RProgram
aNormalForm prefix (Program (PFun x body) t) = do
  aBody <- aNormalForm prefix body
  return $ Program (PFun x aBody) t
aNormalForm prefix (Program (PIf cond thn els) t) = do
  (defsCond, aCond) <- anfE prefix cond True
  aThn <- aNormalForm prefix thn
  aEls <- aNormalForm prefix els
  return $ foldDefs defsCond (Program (PIf aCond aThn aEls) t) t
aNormalForm prefix (Program (PMatch scr cases) t) = do
  (defsScr, aScr) <- anfE prefix scr True
  aCases <- mapM (\(Case ctor binders e) -> (Case ctor binders) <$> aNormalForm prefix e) cases
  return $ foldDefs defsScr (Program (PMatch aScr aCases) t) t
aNormalForm prefix (Program (PFix xs body) t) = do
  aBody <- aNormalForm prefix body
  return $ Program (PFix xs aBody) t
aNormalForm prefix (Program (PLet x def body) t) = do
  (defsX, aX) <- anfE prefix def False
  aBody <- aNormalForm prefix body
  return $ foldDefs defsX (Program (PLet x aX aBody) t) t
aNormalForm _ (Program PErr t) = return $ Program PErr t
aNormalForm _ (Program PHole t) = error "aNormalForm: got a hole"
aNormalForm prefix eTerm@(Program _ t) = do
  (defs, a) <- anfE prefix eTerm True
  return $ foldDefs defs a t
  
foldDefs defs body t = foldr (\(name, def) p -> Program (PLet name def p) t) body defs
  
-- | 'anfE' @p varRequired@: convert E-term @p@ to a list of bindings and either a variable (if @varRequired@) or a flat application (if not @varRequired@)
anfE :: MonadHorn s => Id -> RProgram -> Bool -> Explorer s ([(Id, RProgram)], RProgram)
anfE prefix p@(Program (PSymbol x) t) _ = return ([], p)
anfE prefix (Program (PApp pFun pArg) t) varRequired = do
  (defsFun, xFun) <- anfE prefix pFun False
  (defsArg, xArg) <- anfE prefix pArg True
  if varRequired
    then do
      tmp <- freshId prefix
      return (defsFun ++ defsArg ++ [(tmp, Program (PApp xFun xArg) t)], (Program (PSymbol tmp) t))
    else return (defsFun ++ defsArg, (Program (PApp xFun xArg) t))
anfE prefix p@(Program (PFun _ _) t) _ = do -- A case for abstraction, which can appear in applications and let-bindings
  p' <- aNormalForm prefix p
  return ([], p')    
anfE _ p _ = error $ unwords ["anfE: not an E-term or abstraction", show p]

-- ToDo: replace this with TypeChecker functionality
reconstructE :: MonadHorn s => Environment -> RType -> Explorer s RProgram
reconstructE env t = do
  oldGoals <- use auxGoals
  auxGoals .= []
  (finalEnv, p) <- generateE env t
  (Program pTerm pTyp) <- fillInAuxGoals p
  auxGoals .= oldGoals
  pTyp' <- runInSolver $ currentAssignment pTyp
  return $ Program pTerm pTyp'

fillInAuxGoals :: MonadHorn s => RProgram -> Explorer s RProgram
fillInAuxGoals pMain = do
  pAuxs <- reconstructAuxGoals
  return $ foldl (\e2 (x, e1) -> insertAuxSolution x e1 e2) pMain pAuxs
  where
    reconstructAuxGoals = do
      goals <- use auxGoals
      writeLog 2 $ text "Auxiliary goals are:" $+$ vsep (map pretty goals)
      case goals of
        [] -> return []
        (g : gs) -> do
            auxGoals .= gs
            -- let g' = g {
                          -- gEnvironment = removeVariable (gName goal) (gEnvironment g)  -- remove recursive calls of the main goal
                       -- }
            writeLog 1 $ text "PICK AUXILIARY GOAL" <+> pretty g
            p <- reconstructTopLevel g
            rest <- reconstructAuxGoals
            return $ (gName g, p) : rest
            
-- | 'insertAuxSolution' @x pAux pMain@: insert solution @pAux@ to the auxiliary goal @x@ into @pMain@;
-- @pMain@ is assumed to contain either a "let x = ??" or "f x ..."
insertAuxSolution :: Id -> RProgram -> RProgram -> RProgram
insertAuxSolution x pAux (Program body t) = flip Program t $ 
  case body of
    PLet y def p -> if x == y 
                    then PLet x pAux p
                    else PLet y (ins def) (ins p) 
    PSymbol y -> if x == y
                    then content $ pAux
                    else body
    PApp p1 p2 -> PApp (ins p1) (ins p2)
    PFun y p -> PFun y (ins p)
    PIf c p1 p2 -> PIf (ins c) (ins p1) (ins p2)
    PMatch s cases -> PMatch (ins s) (map (\(Case c args p) -> Case c args (ins p)) cases)
    PFix ys p -> PFix ys (ins p)
    _ -> body  
  where
    ins = insertAuxSolution x pAux