{-# LANGUAGE TemplateHaskell #-}
-- | Refinement type reconstruction for programs with holes
module Synquid.TypeChecker (reconstruct, reconstructTopLevel) where

import Synquid.Logic
import Synquid.Type hiding (set)
import Synquid.Program
import Synquid.Types.Error
import Synquid.SolverMonad
import Synquid.TypeConstraintSolver hiding (freshId, freshVar)
import Synquid.Explorer
import Synquid.Util
import Synquid.Pretty
import Synquid.Resolver
import Synquid.Types.Logic
import Synquid.Types.Program
import Synquid.Types.Params
import Synquid.Types.Explorer
import Synquid.Types.Type
import Synquid.Types.Rest
-- import Synquid.Worlds

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Bifunctor
import qualified Data.Foldable as F
import Control.Monad.Logic
import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative hiding (empty)
import Control.Lens
import qualified Text.PrettyPrint.ANSI.Leijen as L
import Development.Placeholders
import Debug.Trace

-- | 'reconstruct' @eParams tParams goal@ : reconstruct missing types and terms in the body of @goal@ so that it represents a valid type judgment;
-- return a type error if that is impossible. This is the top-level synthesis function.
reconstruct :: MonadHorn s => ExplorerParams -> TypingParams -> Goal -> s (Either ErrorMessage RWProgram)
reconstruct eParams tParams goal = do
    initTS <- initTypingState (gEnvironment goal) (gSpec goal)
    runExplorer (eParams { _sourcePos = gSourcePos goal }) tParams (Reconstructor reconstructTopLevel) initTS go
  where
    go :: MonadHorn s => Explorer s RWProgram
    go = do
      pMain <- reconstructTopLevel goal { gDepth = _auxDepth eParams }     -- Reconstruct the program
      p <- flip insertAuxSolutions pMain <$> (use solvedAuxGoals)            -- Insert solutions for auxiliary goals stored in @solvedAuxGoals@
      runInSolver $ finalizeWProgram p                                      -- Substitute all type/predicates variables and unknowns

reconstructTopLevel :: MonadHorn s => Goal -> Explorer s RWProgram
reconstructTopLevel (Goal funName env (ForallT a sch) impl depth pos s) =
    reconstructTopLevel (Goal funName (addTypeVar a env) sch impl depth pos s)
reconstructTopLevel (Goal funName env (ForallP sig sch) impl depth pos s) =
    reconstructTopLevel (Goal funName (addBoundPredicate sig env) sch impl depth pos s)
reconstructTopLevel g@(Goal funName env (Monotype typ@FunctionT {}) impl depth _ synth)
  | isFunctionType typ || isIntersection typ =
    local (set (_1 . auxDepth) depth) (reconstructFix g)
reconstructTopLevel (Goal _ env (Monotype t) impl depth _ _) = do
    -- TODO(mj)2021-06-09: Make sure this does what it's supposed to
    let t' = checkWellFormedIntersection t
    let impl' = convertToNWorlds impl 1
    local (set (_1 . auxDepth) depth) $ reconstructI [(env, t')] impl'

-- | Add the fix rule, and split worlds if necessary.
reconstructFix :: MonadHorn s => Goal -> Explorer s RWProgram
reconstructFix (Goal funName env (Monotype typ) impl depth _ synth) = do
  let typ' = renameAsImpl (isBound env) impl typ
  recCalls <- runInSolver (currentAssignment typ') >>= recursiveCalls synth
  polymorphic <- asks . view $ _1 . polyRecursion
  predPolymorphic <- asks . view $ _1 . predPolyRecursion
  let tvs = env ^. boundTypeVars
  let pvs = env ^. boundPredicates
  let predGeneralized sch = if predPolymorphic then foldr ForallP sch pvs else sch -- Version of @t'@ generalized in bound predicate variables of the enclosing function
  let typeGeneralized sch = if polymorphic then foldr ForallT sch tvs else sch -- Version of @t'@ generalized in bound type variables of the enclosing function
  let env' = foldr (\(f, t) -> addPolyVariable f (typeGeneralized . predGeneralized . Monotype $ t) . (shapeConstraints %~ Map.insert f (shape typ'))) env recCalls
  $(todo "Should the number of worlds in the ctx be 1 or n?")
  let ctx p = if null recCalls then p else Program (PFix (map fst recCalls) p) [typ']
  let ws = makeWorlds env' typ'
  let impl' = convertToNWorlds impl (length ws)
  p <- inContext ctx $ reconstructI ws impl'
  return $ ctx p

  where


    -- | 'recursiveCalls' @t@: name-type pairs for recursive calls to a function with type @t@ (0 or 1)
    recursiveCalls False t = return [(funName, t)]
    recursiveCalls _ t = do
      fixStrategy <- asks . view $ _1 . fixStrategy
      case fixStrategy of
        AllArguments -> do recType <- fst <$> recursiveTypeTuple t ffalse; if recType == t then return [] else return [(funName, recType)]
        FirstArgument -> do recType <- recursiveTypeFirst t; if recType == t then return [] else return [(funName, recType)]
        DisableFixpoint -> return []
        Nonterminating -> return [(funName, t)]

    -- | 'recursiveTypeTuple' @t fml@: type of the recursive call to a function of type @t@ when a lexicographic tuple of all recursible arguments decreases;
    -- @fml@ denotes the disjunction @x1' < x1 || ... || xk' < xk@ of strict termination conditions on all previously seen recursible arguments to be added to the type of the last recursible argument;
    -- the function returns a tuple of the weakend type @t@ and a flag that indicates if the last recursible argument has already been encountered and modified
    recursiveTypeTuple (FunctionT x tArg tRes) fml =
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
    recursiveTypeTuple (AndT l r) fml = do
      (l', seenLastLeft) <- recursiveTypeTuple l fml
      (r', seenLastRight) <- recursiveTypeTuple r fml
      return $ (AndT l' r', seenLastLeft || seenLastRight)
    recursiveTypeTuple t _ = return (t, False)

    -- | 'recursiveTypeFirst' @t fml@: type of the recursive call to a function of type @t@ when only the first recursible argument decreases
    recursiveTypeFirst (FunctionT x tArg tRes) =
      case terminationRefinement x tArg of
        Nothing -> FunctionT x tArg <$> recursiveTypeFirst tRes
        Just (argLt, _) -> do
          y <- freshVar env "x"
          return $ FunctionT y (addRefinement tArg argLt) (renameVar (isBound env) x y tArg tRes)
    recursiveTypeFirst (AndT l r) = do
      l' <- recursiveTypeFirst l
      r' <- recursiveTypeFirst r
      return $ AndT l' r'
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

-- | 'reconstructI' @env t impl@ :: reconstruct unknown types and terms in a judgment
-- @env@ |- @impl@ :: @t@ where @impl@ is a (possibly) introduction term
-- (top-down phase of bidirectional reconstruction)
reconstructI :: MonadHorn s => [World] -> RWProgram  -> Explorer s RWProgram
reconstructI ws (Program p [AnyT]) = reconstructI' ws p
reconstructI ws (Program p t') = do
  let envs = map fst ws
  let envStr = addListToZip ws t'
  t'' <- checkAnnotation envStr p
  reconstructI' (zip envs t'') p

reconstructI' :: MonadHorn s => [World] -> BareProgram [RType] -> Explorer s RWProgram
reconstructI' ws PErr = generateError $ fst $ head ws
reconstructI' ws PHole = (generateError $ fst $ head ws) `mplus` generateI ws
reconstructI' ws (PLet x iDef@(Program PFun{} _) iBody) = do
    let envs = map fst ws
    let ts = map snd ws
    lambdaLets %= Map.insert x (envs, iDef)
    let ctx p = Program (PLet x uHoleWorld p) ts
    pBody <- inContext ctx $ reconstructI ws iBody
    return $ ctx pBody
-- TODO(mj)2021-06-09: Could we ever have a mix of let and non-let types?
reconstructI' ws impl
    | any (isContextual . snd) ws =
        let ws' = flip map ws $ \(env, t) ->
                case t of
                    LetT x tDef tBody -> (addVariable x tDef env, tBody)
                    _ -> (env, t)
         in reconstructI' ws impl
    -- This intersection splitting is generic enough to handle intersections whereever.
    | any (isIntersection . snd) ws = do
        let ws' =
                concatMap
                    ( \(env, t) ->
                        let isects = intersectionToList t
                            n = length isects
                         in zip (replicate n env) isects
                    )
                    ws
        reconstructI' ws' impl
reconstructI' ws@((_,FunctionT{}):_) impl =
    let envs = map fst ws
        ts = map snd ws
        in case impl of
            PFun y impl -> do
                let ctx p = Program (PFun y p) ts
                let ws' = flip map ws $ \(env, FunctionT _ tArg tRes) ->
                        (unfoldAllVariables $ addVariable y tArg env, tRes)
                pBody <- inContext ctx $ reconstructI ws' impl
                return $ ctx pBody
            PSymbol f -> do
                fun <- etaExpand ts f
                reconstructI' ws $ content fun
            _ ->
                throwErrorWithDescription $
                    text "Cannot assign function type" </> squotes (pretty ts)
                        </> text "to non-lambda term"
                        </> squotes (pretty $ untypedWorld impl)
reconstructI' ws@((_,ScalarT{}):_) impl = case impl of
    PFun _ _ -> throwErrorWithDescription $ text "Cannot assign non-function type" </> squotes (pretty ts) </>
                           text "to lambda term" </> squotes (pretty $ untypedWorld impl)

    PLet x iDef iBody -> do -- E-term let (since lambda-let was considered before)
        let anyWorlds = zip envs (repeat AnyT)
        pDef <- inContext (\p -> Program (PLet x p (Program PHole ts)) ts) $ reconstructETopLevel anyWorlds iDef
        let ws' = zipWith embedContext envs (typeOf pDef)
        let tDefs = map snd ws'
        let ws'' = map (\(env', tDef, t) -> (addVariable x tDef env', t)) (addListToZip ws' ts)
        pBody <- inContext (\p -> Program (PLet x pDef p) ts) $ reconstructI ws'' iBody
        return $ Program (PLet x pDef pBody) ts

--   PIf (Program PHole AnyT) iThen iElse -> do
--     cUnknown <- Unknown Map.empty <$> freshId "C"
--     addConstraint $ WellFormedCond env cUnknown
--     pThen <- inContext (\p -> Program (PIf (Program PHole boolAll) p (Program PHole t)) t) $ reconstructI (addAssumption cUnknown env) t iThen
--     cond <- conjunction <$> currentValuation cUnknown
--     pCond <- inContext (\p -> Program (PIf p uHole uHole) t) $ generateCondition env cond
--     pElse <- optionalInPartial t $ inContext (\p -> Program (PIf pCond pThen p) t) $ reconstructI (addAssumption (fnot cond) env) t iElse
--     return $ Program (PIf pCond pThen pElse) t

--   PIf iCond iThen iElse -> do
--     pCond <- inContext (\p -> Program (PIf p (Program PHole t) (Program PHole t)) t) $ reconstructETopLevel env (ScalarT BoolT ftrue) iCond
--     let (env', ScalarT BoolT cond) = embedContext env $ typeOf pCond
--     pThen <- inContext (\p -> Program (PIf pCond p (Program PHole t)) t) $ reconstructI (addAssumption (substitute (Map.singleton valueVarName ftrue) cond) $ env') t iThen
--     pElse <- inContext (\p -> Program (PIf pCond pThen p) t) $ reconstructI (addAssumption (substitute (Map.singleton valueVarName ffalse) cond) $ env') t iElse
--     return $ Program (PIf pCond pThen pElse) t

--   PMatch iScr iCases -> do
--     (consNames, consTypes) <- unzip <$> checkCases Nothing iCases
--     let scrT = refineTop env $ shape $ lastType $ head consTypes
--     pScrutinee <- inContext (\p -> Program (PMatch p []) t) $ reconstructETopLevel env scrT iScr
--     let (env', tScr) = embedContext env (typeOf pScrutinee)
--     let scrutineeSymbols = symbolList pScrutinee
--     let isGoodScrutinee = (not $ head scrutineeSymbols `elem` consNames) &&                 -- Is not a value
--                           (any (not . flip Set.member (env ^. constants)) scrutineeSymbols) -- Has variables (not just constants)
--     when (not isGoodScrutinee) $ throwErrorWithDescription $ text "Match scrutinee" </> squotes (pretty pScrutinee) </> text "is constant"

--     (env'', x) <- toVar (addScrutinee pScrutinee env') pScrutinee
--     pCases <- zipWithM (reconstructCase env'' x pScrutinee t) iCases consTypes
--     return $ Program (PMatch pScrutinee pCases) t

    _ -> reconstructETopLevel ws (untypedWorld impl)

    where
        envs = map fst ws
        ts = map snd ws
--     -- Check that all constructors are known and belong to the same datatype
--     checkCases mName (Case consName args _ : cs) = case Map.lookup consName (allSymbols env) of
--       Nothing -> throwErrorWithDescription $ text "Not in scope: data constructor" </> squotes (text consName)
--       Just consSch -> do
--                         consT <- instantiate env consSch True args -- Set argument names in constructor type to user-provided binders
--                         case lastType consT of
--                           (ScalarT (DatatypeT dtName _ _) _) -> do
--                             case mName of
--                               Nothing -> return ()
--                               Just name -> if dtName == name
--                                              then return ()
--                                              else throwErrorWithDescription $ text "Expected constructor of datatype" </> squotes (text name) </>
--                                                                text "and got constructor" </> squotes (text consName) </>
--                                                                text "of datatype" </> squotes (text dtName)
--                             if arity (toMonotype consSch) /= length args
--                               then throwErrorWithDescription $ text "Constructor" </> squotes (text consName)
--                                             </> text "expected" </> pretty (arity (toMonotype consSch)) </> text "binder(s) and got" <+> pretty (length args)
--                               else ((consName, consT) :) <$> checkCases (Just dtName) cs
--                           _ -> throwErrorWithDescription $ text "Not in scope: data constructor" </> squotes (text consName)
--     checkCases _ [] = return []

reconstructCase :: MonadHorn s => Environment -> Formula -> RProgram -> TypeVector -> Case RType -> RType -> Explorer s (Case RType)
reconstructCase = $(todo "reconstructCase")
-- reconstructCase env scrVar pScrutinee t (Case consName args iBody) consT = do
--   runInSolver $ matchConsType (lastType consT) (typeOf pScrutinee)
--   consT' <- runInSolver $ currentAssignment consT
--   (syms, ass) <- caseSymbols env scrVar args consT'
--   let caseEnv = foldr (uncurry addVariable) (addAssumption ass env) syms
--   pCaseExpr <- local (over (_1 . matchDepth) (-1 +)) $
--                inContext (\p -> Program (PMatch pScrutinee [Case consName args p]) t) $
--                reconstructI caseEnv t iBody
--   return $ Case consName args pCaseExpr

-- | 'reconstructE' @env t impl@ :: reconstruct unknown types and terms in a judgment
-- @env@ |- @impl@ :: @t@ where @impl@ is an elimination term
-- (bottom-up phase of bidirectional reconstruction)
reconstructETopLevel :: MonadHorn s => [World] -> RWProgram  -> Explorer s RWProgram
-- reconstructETopLevel = $(todo "reconstructETopLevel with worlds")
reconstructETopLevel ws impl = do
  (Program pTerm pTyps) <- reconstructE ws impl
  generateAuxGoals
  pTyps' <- mapM (runInSolver . currentAssignment) pTyps
  return $ Program pTerm pTyps'

reconstructE :: MonadHorn s => [World]-> RWProgram  -> Explorer s RWProgram
reconstructE ws (Program p [AnyT]) = reconstructE' ws p
reconstructE ws (Program p t') = do
  ts'' <- checkAnnotation (addListToZip ws t') p
  let ws' = zip (map fst ws) ts''
  reconstructE' ws' p

reconstructE' :: MonadHorn s => [World] -> BareProgram TypeVector -> Explorer s RWProgram
-- reconstructE' _ (AndT _ _) _ = error "and E-term cannot have an intersection"
reconstructE' ws PHole = do
  d <- asks . view $ _1 . eGuessDepth
  generateEUpTo ws d
-- {- Var Rule -}
reconstructE' ws (PSymbol name) = do
  checkSymbol ws name
reconstructE' ws (PApp iFun iArg) = do
    pApp <- generateApp (False, id) ws (`reconstructE` iFun) (`reconstructE` iArg)
    checkE ws pApp
    return pApp
-- reconstructE' ws (PApp iFun iArg) = do
--     x <- freshVar (fst $ head ws) "x" -- freshVar just looks at the symbol names.
--     let retTyps = map snd ws
--     let ws' = map (second (FunctionT x AnyT)) ws
--     pFun <- inContext (\p -> Program (PApp p uHoleWorld) retTyps)
--             $ reconstructE ws' iFun
-- --   let FunctionT x tArg tRes = typeOf pFun
--     let funTypes = typeOf pFun
--     let argTypes' = map argType funTypes
--     let retTypes' = map resType funTypes
--     let envs = map fst ws

--     pApp <- if argTypes' & head & isFunctionType
--         then do -- Higher-order argument: its value is not required for the function type, enqueue an auxiliary goal
--             $(todo "HOF goals, should they be world goals? I think yes.")
--             -- d <- asks . view $ _1 . auxDepth
--             -- pArg <- generateHOArg env (d - 1) tArg iArg
--             -- return $ Program (PApp pFun pArg) tRes
--         else do -- First-order argument: generate now
--             let argWorlds = zip envs argTypes'
--             pArg <- inContext (\p -> Program (PApp pFun p) retTyps)
--                 $ reconstructE argWorlds iArg
--             let ws'' = zip envs retTypes'
--             let tRes' = appTypes ws'' pArg x
--             return $ Program (PApp pFun pArg) tRes'
--     checkE ws pApp
--     return pApp
--     where
        -- generateHOArg env d tArg iArg = case content iArg of
        --     PSymbol f -> do
        --         lets <- use lambdaLets
        --         case Map.lookup f lets of
        --             Nothing -> do -- This is a function from the environment, with a known type: add its eta-expansion as an aux goal
        --                         impl <- etaExpand tArg f
        --                         _ <- enqueueGoal env tArg impl d
        --                         return ()
        --             Just (env', def) -> auxGoals %= ((Goal f env' (Monotype tArg) def d noPos True) :) -- This is a locally defined function: add an aux goal with its body
        --         return iArg
        --     _ -> enqueueGoal env tArg iArg d -- HO argument is an abstraction: enqueue a fresh goal

-- reconstructE' env typ impl =
--   throwErrorWithDescription $ text "Expected application term of type" </> squotes (pretty typ) </>
--                                           text "and got" </> squotes (pretty $ untyped impl)
reconstructE' _ _ = $(todo "reconstructE' with worlds")

-- | 'checkAnnotation' @ws:=(env, t, t'):.. p@ : if user annotation @t'@ for program @p@ is a subtype of the goal type @t@,
-- return resolved @t'@, otherwise fail
-- @p@ is expected to be untyped
checkAnnotation :: MonadHorn s => [(Environment, RType, RType)] -> BareProgram TypeVector  -> Explorer s TypeVector
checkAnnotation ws p = $(todo "checkAnnotation with worlds")
-- checkAnnotation ws p = do
--   tass <- use (typingState . typeAssignment)
--   case resolveRefinedType (typeSubstituteEnv tass env) t' of
--     Left err -> throwError err
--     Right t'' -> do
--       ctx <- asks . view $ _1 . context
--       writeLog 2 $ text "Checking consistency of type annotation" <+> pretty t'' <+> text "with" <+> pretty t <+> text "in" $+$ pretty (ctx (Program p t''))
--       addConstraint $ Subtype env t'' t True ""

--       fT <- runInSolver $ finalizeType t
--       fT'' <- runInSolver $ finalizeType t''
--       pos <- asks . view $ _1 . sourcePos
--       typingState . errorContext .= (pos, text "when checking consistency of type annotation" </> pretty fT'' </> text "with" </> pretty fT </> text "in" $+$ pretty (ctx (Program p t'')))
--       runInSolver solveTypeConstraints
--       typingState . errorContext .= (noPos, empty)

--       tass' <- use (typingState . typeAssignment)
--       return $ intersection (isBound env) t'' (typeSubstitute tass' t)

-- | 'etaExpand' @t@ @f@: for a symbol @f@ of a function type @t@, the term @\X0 . ... \XN . f X0 ... XN@ where @f@ is fully applied
etaExpand ts f = do
  args <- replicateM (arity (head ts)) (freshId "X")
  let body = foldl (\e1 e2 -> untypedWorld $ PApp e1 e2) (untypedWorld (PSymbol f)) (map (untypedWorld . PSymbol) args)
  return $ foldr (\x p -> untypedWorld $ PFun x p) body args

-- | 'insertAuxSolution' @pAuxs pMain@: insert solutions stored in @pAuxs@ indexed by names of auxiliary goals @x@ into @pMain@;
-- @pMain@ is assumed to contain either a "let x = ??" or "f x ...", where "x" is an auxiliary goal name
insertAuxSolutions :: Map Id (Program t) -> Program t -> Program t
insertAuxSolutions pAuxs (Program body t) = flip Program t $
  case body of
    PLet y def p -> case Map.lookup y pAuxs of
                      Nothing -> PLet y (ins def) (ins p)
                      Just pAux -> PLet y pAux (insertAuxSolutions (Map.delete y pAuxs) p)
    PSymbol y -> case Map.lookup y pAuxs of
                    Nothing -> body
                    Just pAux -> content $ pAux
    PApp p1 p2 -> PApp (ins p1) (ins p2)
    PFun y p -> PFun y (ins p)
    PIf c p1 p2 -> PIf (ins c) (ins p1) (ins p2)
    PMatch s cases -> PMatch (ins s) (map (\(Case c args p) -> Case c args (ins p)) cases)
    PFix ys p -> PFix ys (ins p)
    _ -> body
  where
    ins = insertAuxSolutions pAuxs
