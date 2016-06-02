{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}

-- | Incremental solving of subtyping and well-formedness constraints
module Synquid.TypeConstraintSolver (
  ErrorMessage,
  TypingParams (..),
  TypingState,
  typingConstraints,
  typeAssignment,
  qualifierMap,
  candidates,
  errorContext,
  isFinal,
  TCSolver,
  runTCSolver,
  initTypingState,
  addTypingConstraint,
  addFixedUnknown,
  setUnknownRecheck,
  solveTypeConstraints,
  solveAllCandidates,
  matchConsType,
  hasPotentialScrutinees,
  freshId,
  freshVar,
  currentAssignment,
  finalizeType,
  finalizeProgram,
  initEnv,
  allScalars
) where

import Synquid.Logic
import Synquid.Type
import Synquid.Program
import Synquid.Error
import Synquid.Pretty
import Synquid.SolverMonad
import Synquid.Util
import Synquid.Resolver (addAllVariables)

import Data.Maybe
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Except
import Control.Applicative hiding (empty)
import Control.Lens hiding (both)
import Debug.Trace

{- Interface -}

-- | Parameters of type constraint solving
data TypingParams = TypingParams {
  _condQualsGen :: Environment -> [Formula] -> QSpace,              -- ^ Qualifier generator for conditionals
  _matchQualsGen :: Environment -> [Formula] -> QSpace,             -- ^ Qualifier generator for match scrutinees
  _typeQualsGen :: Environment -> Formula -> [Formula] -> QSpace,   -- ^ Qualifier generator for types
  _predQualsGen :: Environment -> [Formula] -> [Formula] -> QSpace, -- ^ Qualifier generator for bound predicates
  _tcSolverLogLevel :: Int    -- ^ How verbose logging is  
}

makeLenses ''TypingParams

-- | State of type constraint solving
data TypingState = TypingState {
  -- Persistent state:
  _typingConstraints :: [Constraint],           -- ^ Typing constraints yet to be converted to horn clauses
  _typeAssignment :: TypeSubstitution,          -- ^ Current assignment to free type variables
  _predAssignment :: Substitution,              -- ^ Current assignment to free predicate variables  _qualifierMap :: QMap,
  _qualifierMap :: QMap,                        -- ^ Current state space for predicate unknowns
  _candidates :: [Candidate],                   -- ^ Current set of candidate liquid assignments to unknowns
  _initEnv :: Environment,                      -- ^ Initial environment
  _idCount :: Map String Int,                   -- ^ Number of unique identifiers issued so far
  _isFinal :: Bool,                             -- ^ Has the entire program been seen?
  -- Temporary state:
  _simpleConstraints :: [Constraint],           -- ^ Typing constraints that cannot be simplified anymore and can be converted to horn clauses or qualifier maps
  _hornClauses :: [Formula],                    -- ^ Horn clauses generated from subtyping constraints
  _consistencyChecks :: [Formula],              -- ^ Formulas generated from type consistency constraints
  _errorContext :: (SourcePos, Doc)             -- ^ Information to be added to all type errors
}

makeLenses ''TypingState

-- | Computations that solve type constraints, parametrized by the the horn solver @s@
type TCSolver s = StateT TypingState (ReaderT TypingParams (ExceptT ErrorMessage s))

-- | 'runTCSolver' @params st go@ : execute a typing computation @go@ with typing parameters @params@ in a typing state @st@
runTCSolver :: TypingParams -> TypingState -> TCSolver s a -> s (Either ErrorMessage (a, TypingState))
runTCSolver params st go = runExceptT $ runReaderT (runStateT go st) params  

-- | Initial typing state in the initial environment @env@
initTypingState :: MonadHorn s => Environment -> s TypingState
initTypingState env = do
  initCand <- initHornSolver
  return $ TypingState {
    _typingConstraints = [],
    _typeAssignment = Map.empty,
    _predAssignment = Map.empty,
    _qualifierMap = Map.empty,
    _candidates = [initCand],
    _initEnv = env,
    _idCount = Map.empty,
    _isFinal = True,
    _simpleConstraints = [],
    _hornClauses = [],
    _consistencyChecks = [],
    _errorContext = (noPos, empty)
  }

-- | Impose typing constraint @c@ on the programs
addTypingConstraint c = over typingConstraints (nub . (c :))  

-- | Solve @typingConstraints@: either strengthen the current candidates and return shapeless type constraints or fail
solveTypeConstraints :: MonadHorn s => TCSolver s ()
solveTypeConstraints = do
  simplifyAllConstraints
  
  scs <- use simpleConstraints
  writeLog 2 (text "Simple Constraints" $+$ (vsep $ map pretty scs))  
        
  tass <- use typeAssignment
  writeLog 2 (text "Type assignment" $+$ vMapDoc text pretty tass)
  
  processAllPredicates
  
  pass <- use predAssignment
  writeLog 2 (text "Pred assignment" $+$ vMapDoc text pretty pass)        
  
  processAllConstraints
  solveHornClauses
  checkTypeConsistency  
  clearTempState  
      
{- Implementation -}      
      
-- | Decompose and unify typing constraints; 
-- return shapeless type constraints: constraints involving only free type variables, which impose no restrictions yet, but might in the future
simplifyAllConstraints :: MonadHorn s => TCSolver s () 
simplifyAllConstraints = do
  tcs <- use typingConstraints
  writeLog 2 (text "Typing Constraints" $+$ (vsep $ map pretty tcs))
  typingConstraints .= []
  tass <- use typeAssignment
  mapM_ simplifyConstraint tcs
    
  -- If type assignment has changed, we might be able to process more shapeless constraints:
  tass' <- use typeAssignment
  when (Map.size tass' > Map.size tass) simplifyAllConstraints
  
-- | Assign unknowns to all free predicate variables  
processAllPredicates :: MonadHorn s => TCSolver s ()
processAllPredicates = do
  tcs <- use typingConstraints
  typingConstraints .= []
  mapM_ processPredicate tcs
    
-- | Convert simple typing constraints into horn clauses and qualifier maps
processAllConstraints :: MonadHorn s => TCSolver s ()
processAllConstraints = do
  tcs <- uses simpleConstraints nub
  let (subs, wfs) = partition isSubtyping tcs
  mapM_ processConstraint (wfs ++ subs) -- process well-formedness constraints first
  where
    isSubtyping (Subtype _ _ _ _) = True
    isSubtyping _ = False
  
-- | Signal type error  
throwError :: MonadHorn s => Doc -> TCSolver s ()  
throwError msg = do
  (pos, ec) <- use errorContext
  lift $ lift $ throwE $ ErrorMessage TypeError pos (msg $+$ ec)

-- | Refine the current liquid assignments using the horn clauses
solveHornClauses :: MonadHorn s => TCSolver s ()
solveHornClauses = do
  clauses <- use hornClauses
  qmap <- use qualifierMap
  cands <- use candidates
  env <- use initEnv
  cands' <- lift . lift . lift $ refineCandidates clauses qmap (instantiateConsAxioms env) cands
    
  when (null cands') (throwError $ text "Cannot find sufficiently strong refinements")
  candidates .= cands'
  
solveAllCandidates :: MonadHorn s => TCSolver s ()  
solveAllCandidates = do
  cands <- use candidates
  cands' <- concat <$> mapM solveCandidate cands
  candidates .= cands'
  where
    solveCandidate c@(Candidate s valids invalids _) = 
      if null invalids
        then return [c]
        else do
          qmap <- use qualifierMap
          env <- use initEnv        
          cands' <- lift . lift . lift $ refineCandidates [] qmap (instantiateConsAxioms env) [c]
          concat <$> mapM solveCandidate cands'

-- | Filter out liquid assignments that are too strong for current consistency checks  
checkTypeConsistency :: MonadHorn s => TCSolver s ()  
checkTypeConsistency = do
  clauses <- use consistencyChecks
  cands <- use candidates
  env <- use initEnv  
  cands' <- lift . lift . lift $ checkCandidates True clauses (instantiateConsAxioms env) cands
  when (null cands') (throwError $ text "Found inconsistent refinements")
  candidates .= cands'

-- | Simplify @c@ into a set of simple and shapeless constraints, possibly extended the current type assignment or predicate assignment
simplifyConstraint :: MonadHorn s => Constraint -> TCSolver s ()
simplifyConstraint c = do
  tass <- use typeAssignment
  pass <- use predAssignment
  simplifyConstraint' tass pass c

-- Any type: drop
simplifyConstraint' _ _ (Subtype _ _ AnyT _) = return ()
simplifyConstraint' _ _ c@(Subtype _ AnyT _ _) = return ()
simplifyConstraint' _ _ c@(WellFormed _ AnyT) = return ()
-- Well-formedness of a known predicate drop  
simplifyConstraint' _ pass c@(WellFormedPredicate _ _ p) | p `Map.member` pass = return ()
  
-- Type variable with known assignment: substitute
simplifyConstraint' tass _ (Subtype env tv@(ScalarT (TypeVarT a) _) t consistent) | a `Map.member` tass
  = simplifyConstraint (Subtype env (typeSubstitute tass tv) t consistent)
simplifyConstraint' tass _ (Subtype env t tv@(ScalarT (TypeVarT a) _) consistent) | a `Map.member` tass
  = simplifyConstraint (Subtype env t (typeSubstitute tass tv) consistent)
simplifyConstraint' tass _ (WellFormed env tv@(ScalarT (TypeVarT a) _)) | a `Map.member` tass
  = simplifyConstraint (WellFormed env (typeSubstitute tass tv))
  
-- Two unknown free variables: nothing can be done for now
simplifyConstraint' _ _ c@(Subtype env (ScalarT (TypeVarT a) _) (ScalarT (TypeVarT b) _) _) | not (isBound a env) && not (isBound b env)
  = if a == b
      then error $ show $ text "simplifyConstraint: equal type variables on both sides"
      else ifM (use isFinal) 
            (do -- This is a final pass: assign an arbitrary type to one of the variables
              addTypeAssignment a intAll
              simplifyConstraint c) 
            (modify $ addTypingConstraint c)
simplifyConstraint' _ _ c@(WellFormed env (ScalarT (TypeVarT a) _)) | not (isBound a env) 
  = modify $ addTypingConstraint c
simplifyConstraint' _ _ c@(WellFormedPredicate _ _ _) = modify $ addTypingConstraint c
  
-- Unknown free variable and a type: extend type assignment
simplifyConstraint' _ _ c@(Subtype env (ScalarT (TypeVarT a) _) t _) | not (isBound a env) 
  = unify env a t >> simplifyConstraint c
simplifyConstraint' _ _ c@(Subtype env t (ScalarT (TypeVarT a) _) _) | not (isBound a env) 
  = unify env a t >> simplifyConstraint c

-- Compound types: decompose
simplifyConstraint' _ _ (Subtype env (ScalarT (DatatypeT name (tArg:tArgs) pArgs) fml) (ScalarT (DatatypeT name' (tArg':tArgs') pArgs') fml') consistent)
  = do
      simplifyConstraint (Subtype env tArg tArg' consistent)
      simplifyConstraint (Subtype env (ScalarT (DatatypeT name tArgs pArgs) fml) (ScalarT (DatatypeT name' tArgs' pArgs') fml') consistent)
simplifyConstraint' _ _ (Subtype env (ScalarT (DatatypeT name [] (pArg:pArgs)) fml) (ScalarT (DatatypeT name' [] (pArg':pArgs')) fml') consistent)
  = do
      -- simplifyConstraint (Subtype emptyEnv (int $ pArg) (int $ pArg') consistent) -- Is this a cheat?
      simplifyConstraint (Subtype env (int $ pArg) (int $ pArg') consistent) -- Is this a cheat?
      simplifyConstraint (Subtype env (ScalarT (DatatypeT name [] pArgs) fml) (ScalarT (DatatypeT name' [] pArgs') fml') consistent)      
simplifyConstraint' _ _ (Subtype env (FunctionT x tArg1 tRes1) (FunctionT y tArg2 tRes2) False)
  = do -- TODO: rename type vars
      simplifyConstraint (Subtype env tArg2 tArg1 False)
      if isScalarType tArg1
        then simplifyConstraint (Subtype (addVariable y tArg2 env) (renameVar x y tArg1 tRes1) tRes2 False)
        else simplifyConstraint (Subtype env tRes1 tRes2 False)
simplifyConstraint' _ _ (Subtype env (FunctionT x tArg1 tRes1) (FunctionT y tArg2 tRes2) True)
  = -- TODO: rename type vars
      if isScalarType tArg1
        then simplifyConstraint (Subtype (addVariable x tArg1 env) tRes1 tRes2 True)
        else simplifyConstraint (Subtype env tRes1 tRes2 True)
simplifyConstraint' _ _ c@(WellFormed env (ScalarT (DatatypeT name tArgs _) fml))
  = do
      mapM_ (simplifyConstraint . WellFormed env) tArgs
      simpleConstraints %= (c :)
simplifyConstraint' _ _ (WellFormed env (FunctionT x tArg tRes))
  = do
      simplifyConstraint (WellFormed env tArg)
      simplifyConstraint (WellFormed (addVariable x tArg env) tRes)

-- Simple constraint: return
simplifyConstraint' _ _ c@(Subtype _ (ScalarT baseT _) (ScalarT baseT' _) _) | baseT == baseT' = simpleConstraints %= (c :)
simplifyConstraint' _ _ c@(WellFormed _ (ScalarT baseT _)) = simpleConstraints %= (c :)
simplifyConstraint' _ _ c@(WellFormedCond _ _) = simpleConstraints %= (c :)
simplifyConstraint' _ _ c@(WellFormedMatchCond _ _) = simpleConstraints %= (c :)
-- Otherwise (shape mismatch): fail
simplifyConstraint' _ _ (Subtype _ t t' _) = 
  throwError $ text  "Cannot match shape" <+> squotes (pretty $ shape t) $+$ text "with shape" <+> squotes (pretty $ shape t')

-- | Unify type variable @a@ with type @t@ or fail if @a@ occurs in @t@
unify env a t = if a `Set.member` typeVarsOf t
  then error $ show $ text "simplifyConstraint: type variable occurs in the other type"
  else do
    t' <- fresh env t
    writeLog 2 (text "UNIFY" <+> text a <+> text "WITH" <+> pretty t <+> text "PRODUCING" <+> pretty t')
    addTypeAssignment a t'
    
-- Predicate well-formedness: shapeless or simple depending on type variables  
processPredicate c@(WellFormedPredicate env argSorts p) = do
  tass <- use typeAssignment
  let typeVars = Set.toList $ Set.unions $ map typeVarsOfSort argSorts
  if any (isFreeVariable tass) typeVars
    then do
      writeLog 2 $ text "WARNING: free vars in predicate" <+> pretty c
      modify $ addTypingConstraint c -- Still has type variables: cannot determine shape
    else do                 
      u <- freshId "U"
      addPredAssignment p (Unknown Map.empty u)
      let argSorts' = map (sortSubstitute $ asSortSubst tass) argSorts
      let vars = zipWith Var argSorts' deBrujns
      pq <- asks _predQualsGen
      addQuals u (pq (addAllVariables vars env) vars (allScalars env tass))
  where
    isFreeVariable tass a = not (isBound a env) && not (Map.member a tass)
processPredicate c = modify $ addTypingConstraint c

-- | Convert simple constraint to horn clauses and consistency checks, and update qualifier maps
processConstraint :: MonadHorn s => Constraint -> TCSolver s ()
processConstraint c@(Subtype env (ScalarT baseTL l) (ScalarT baseTR r) False) | baseTL == baseTR
  = if l == ffalse || r == ftrue
      then return ()
      else do
        tass <- use typeAssignment
        pass <- use predAssignment
        qmap <- use qualifierMap
        let subst = sortSubstituteFml (asSortSubst tass) . substitutePredicate pass
        let l' = subst l
        let r' = subst r
        if Set.null $ (predsOf l' `Set.union` predsOf r') Set.\\ (Map.keysSet $ allPredicates env)
          then do
            let relevantVars = potentialVars qmap (l' |&| r')
            emb <- embedding env relevantVars (predsOf r')
            let lhss = uDNF $ conjunction (Set.insert l' emb)
            let clauses = map (|=>| r') lhss
            hornClauses %= (clauses ++)
          else modify $ addTypingConstraint c -- Constraint contains free predicate: add back and wait until more type variables get unified, so predicate variables can be instantiated
processConstraint (Subtype env (ScalarT baseTL l) (ScalarT baseTR r) True) | baseTL == baseTR
  = do -- TODO: abs ref here
      tass <- use typeAssignment
      pass <- use predAssignment
      qmap <- use qualifierMap
      let subst = sortSubstituteFml (asSortSubst tass) . substitutePredicate pass
      let l' = subst l
      let r' = subst r
      if l' == ftrue || r' == ftrue
        then return ()
        else do
          let relevantVars = potentialVars qmap (l' |&| r')
          emb <- embedding env relevantVars Set.empty
          let clause = conjunction (Set.insert l' $ Set.insert r' emb)
          consistencyChecks %= (clause :)
processConstraint (WellFormed env t@(ScalarT baseT fml)) 
  = case fml of
      Unknown _ u -> do      
        qmap <- use qualifierMap
        tass <- use typeAssignment
        tq <- asks _typeQualsGen
        -- Only add qualifiers if it's a new variable; multiple well-formedness constraints could have been added for constructors
        let env' = addVariable valueVarName t env
        when (not $ Map.member u qmap) $ addQuals u (tq env' (Var (toSort baseT) valueVarName) (allScalars env tass))
      _ -> return ()
processConstraint (WellFormedCond env (Unknown _ u))
  = do
      tass <- use typeAssignment
      cq <- asks _condQualsGen
      addQuals u (cq env (allScalars env tass))
processConstraint (WellFormedMatchCond env (Unknown _ u))
  = do
      tass <- use typeAssignment
      mq <- asks _matchQualsGen
      addQuals u (mq env (allPotentialScrutinees env tass))
processConstraint c = error $ show $ text "processConstraint: not a simple constraint" <+> pretty c

-- | 'allScalars' @env@ : logic terms for all scalar symbols in @env@
allScalars :: Environment -> TypeSubstitution -> [Formula]
allScalars env tass = catMaybes $ map toFormula $ Map.toList $ symbolsOfArity 0 env
  where
    toFormula (_, ForallT _ _) = Nothing
    toFormula (x, Monotype t) = case typeSubstitute tass t of
      ScalarT IntT  (Binary Eq _ (IntLit n)) -> Just $ IntLit n
      ScalarT BoolT (Var _ _) -> Just $ BoolLit True
      ScalarT BoolT (Unary Not (Var _ _)) -> Just $ BoolLit False      
      ScalarT b _ -> Just $ Var (toSort b) x
      _ -> Nothing
    
-- | 'allPotentialScrutinees' @env@ : logic terms for all scalar symbols in @env@
allPotentialScrutinees :: Environment -> TypeSubstitution -> [Formula]
allPotentialScrutinees env tass = catMaybes $ map toFormula $ Map.toList $ symbolsOfArity 0 env
  where
    toFormula (x, Monotype t) = case typeSubstitute tass t of
      ScalarT b@(DatatypeT _ _ _) _ ->
        if Set.member x (env ^. unfoldedVars) && not (Program (PSymbol x) t `elem` (env ^. usedScrutinees))
          then Just $ Var (toSort b) x
          else Nothing
      _ -> Nothing 
    toFormula _ = Nothing
    
hasPotentialScrutinees :: Monad s => Environment -> TCSolver s Bool
hasPotentialScrutinees env = do
  tass <- use typeAssignment
  return $ not $ null $ allPotentialScrutinees env tass
  
-- | Assumptions encoded in an environment    
embedding :: Monad s => Environment -> Set Id -> Set Id -> TCSolver s (Set Formula)
embedding env vars measures = do
    tass <- use typeAssignment
    pass <- use predAssignment
    qmap <- use qualifierMap
    let ass = Set.map (substitutePredicate pass) $ (env ^. assumptions)
    let allVars = vars `Set.union` potentialVars qmap (conjunction ass)
    return $ addBindings tass pass qmap ass allVars
  where
    addBindings tass pass qmap fmls vars = 
      if Set.null vars
        then fmls
        else let (x, rest) = Set.deleteFindMin vars in
              case Map.lookup x allSymbols of
                Nothing -> addBindings tass pass qmap  fmls rest -- Variable not found (useful to ignore value variables)
                Just (Monotype t) -> case typeSubstitute tass t of
                  ScalarT baseT fml -> 
                    let fmls' = Set.fromList $ map (substitute (Map.singleton valueVarName (Var (toSort baseT) x))) 
                                          ((substitutePredicate pass fml) : allMeasurePostconditions measures baseT env) in
                    addBindings tass pass qmap (fmls `Set.union` fmls') (rest `Set.union` potentialVars qmap fml)
                  AnyT -> Set.singleton ffalse
                  _ -> error $ unwords ["embedding: encountered non-scalar variable", x, "in 0-arity bucket"]
    allSymbols = symbolsOfArity 0 env `Map.union` Map.map Monotype (env ^. ghosts)

-- | 'potentialVars' @qmap fml@ : variables of @fml@ if all unknowns get strongest valuation according to @quals@    
potentialVars :: QMap -> Formula -> Set Id
potentialVars qmap fml = Set.map varName $ Set.unions (varsOf fml : map (uVars qmap) (Set.toList $ unknownsOf fml))
  where
    uVars qmap u@(Unknown subst name) = Set.unions (map (varsOf . substitute subst) (lookupQuals qmap qualifiers u))

-- | 'freshId' @prefix@ : fresh identifier starting with @prefix@
freshId :: Monad s => String -> TCSolver s String
freshId prefix = do
  i <- uses idCount (Map.findWithDefault 0 prefix)
  idCount %= Map.insert prefix (i + 1)
  return $ prefix ++ show i
  
freshVar :: Monad s => Environment -> String -> TCSolver s String 
freshVar env prefix = do
  x <- freshId prefix
  if Map.member x (allSymbols env)
    then freshVar env prefix
    else return x

-- | 'fresh' @t@ : a type with the same shape as @t@ but fresh type variables, fresh predicate variables, and fresh unknowns as refinements
fresh :: Monad s => Environment -> RType -> TCSolver s RType
fresh env (ScalarT (TypeVarT a) _) | not (isBound a env) = do
  -- Free type variable: replace with fresh free type variable
  a' <- freshId "A"
  return $ ScalarT (TypeVarT a') ftrue
fresh env (ScalarT baseT _) = do
  baseT' <- freshBase baseT
  -- Replace refinement with fresh predicate unknown:
  k <- freshId "U"
  return $ ScalarT baseT' (Unknown Map.empty k)
  where
    freshBase (DatatypeT name tArgs _) = do
      -- Replace type arguments with fresh types:
      tArgs' <- mapM (fresh env) tArgs
      -- Replace predicate arguments with fresh predicate variables:
      let (DatatypeDef tParams pParams _ _) = (env ^. datatypes) Map.! name
      pArgs' <- mapM (\sig -> freshPred env . map (noncaptureSortSubst tParams (map (toSort . baseTypeOf) tArgs')) . predSigArgSorts $ sig) pParams  
      return $ DatatypeT name tArgs' pArgs'
    freshBase baseT = return baseT
fresh env (FunctionT x tArg tFun) = do
  liftM2 (FunctionT x) (fresh env tArg) (fresh env tFun)
  
freshPred env sorts = do
  p' <- freshId "P"
  modify $ addTypingConstraint (WellFormedPredicate env sorts p')
  let args = zipWith Var sorts deBrujns 
  return $ Pred BoolS p' args  
  
addTypeAssignment tv t = typeAssignment %= Map.insert tv t
addPredAssignment p fml = predAssignment %= Map.insert p fml  
  
addQuals :: MonadHorn s => Id -> QSpace -> TCSolver s ()
addQuals name quals = do
  quals' <- lift . lift . lift $ pruneQualifiers quals
  qualifierMap %= Map.insert name quals'
  
-- | Add unknown @name@ with valuation @valuation@ to solutions of all candidates  
addFixedUnknown :: MonadHorn s => Id -> Set Formula -> TCSolver s ()  
addFixedUnknown name valuation = do
    addQuals name (toSpace Nothing (Set.toList valuation))
    candidates %= map update
  where
    update cand = cand { solution = Map.insert name valuation (solution cand) }
    
-- | Set valuation of unknown @name@ to @valuation@
-- and re-check all potentially affected constraints in all candidates 
setUnknownRecheck :: MonadHorn s => Id -> Set Formula -> TCSolver s ()
setUnknownRecheck name valuation = do
  writeLog 2 $ text "Re-checking candidates after updating" <+> text name
  cands@(cand:_) <- use candidates
  let clauses = Set.filter (\fml -> name `Set.member` (Set.map unknownName (unknownsOf fml))) (validConstraints cand) -- First candidate cannot have invalid constraints
  let cands' = map (\c -> c { solution = Map.insert name valuation (solution c) }) cands
  env <- use initEnv
  cands'' <- lift . lift . lift $ checkCandidates False (Set.toList clauses) (instantiateConsAxioms env) cands'
    
  when (null cands'') (throwError $ text "Re-checking candidates failed")
  candidates .= cands''  
  
-- | 'instantiateConsAxioms' @env fml@ : If @fml@ contains constructor applications, return the set of instantiations of constructor axioms for those applications in the environment @env@ 
instantiateConsAxioms :: Environment -> Formula -> Set Formula  
instantiateConsAxioms env fml = let inst = instantiateConsAxioms env in
  case fml of
    Cons resS@(DataS dtName _) ctor args -> Set.fromList $ map (measureAxiom resS ctor args) (Map.elems $ allMeasuresOf dtName env)
    Unary op e -> inst e
    Binary op e1 e2 -> inst e1 `Set.union` inst e2
    Ite e0 e1 e2 -> inst e0 `Set.union` inst e1 `Set.union` inst e2
    SetLit _ elems -> Set.unions (map inst elems)
    Pred _ p args -> Set.unions $ map inst args
    _ -> Set.empty  
  where
    measureAxiom resS ctor args (MeasureDef inSort _ defs _) = 
      let MeasureCase _ vars body = head $ filter (\(MeasureCase c _ _) -> c == ctor) defs in
      let sParams = map varSortName (sortArgsOf inSort) in -- sort parameters in the datatype declaration
      let sArgs = sortArgsOf resS in -- actual sort argument in the constructor application
      let body' = noncaptureSortSubstFml sParams sArgs body in -- measure definition with actual sorts for all subexpressions
      let subst = Map.fromList $ (valueVarName, Cons resS ctor args) : zip vars args in -- substitute formals for actuals and constructor application for _v    
      substitute subst body'
    
-- | 'matchConsType' @formal@ @actual@ : unify constructor return type @formal@ with @actual@
matchConsType formal@(ScalarT (DatatypeT d vars pVars) _) actual@(ScalarT (DatatypeT d' args pArgs) _) | d == d' 
  = do
      writeLog 2 $ text "Matching constructor type" $+$ pretty formal $+$ text "with scrutinee" $+$ pretty actual
      zipWithM_ (\(ScalarT (TypeVarT a) (BoolLit True)) t -> addTypeAssignment a t) vars args
      zipWithM_ (\(Pred BoolS p _) fml -> addPredAssignment p fml) pVars pArgs
matchConsType t t' = error $ show $ text "matchConsType: cannot match" <+> pretty t <+> text "against" <+> pretty t'
    
currentAssignment :: Monad s => RType -> TCSolver s RType
currentAssignment t = do
  tass <- use typeAssignment
  return $ typeSubstitute tass t
    
-- | Substitute type variables, predicate variables, and predicate unknowns in @t@
-- using current type assignment, predicate assignment, and liquid assignment
finalizeType :: Monad s => RType -> TCSolver s RType
finalizeType t = do
  tass <- use typeAssignment
  pass <- use predAssignment
  sol <- uses candidates (solution . head)
  return $ (typeApplySolution sol . typeSubstitutePred pass . typeSubstitute tass) t
    
-- | Substitute type variables, predicate variables, and predicate unknowns in @p@
-- using current type assignment, predicate assignment, and liquid assignment
finalizeProgram :: Monad s => RProgram -> TCSolver s RProgram
finalizeProgram p = do
  tass <- use typeAssignment
  pass <- use predAssignment
  sol <- uses candidates (solution . head)
  return $ fmap (typeApplySolution sol . typeSubstitutePred pass . typeSubstitute tass) p

-- | Clear temporary typing state    
clearTempState ::  MonadHorn s => TCSolver s ()    
clearTempState = do
  simpleConstraints .= []
  hornClauses .= []
  consistencyChecks .= []    
  
instance Eq TypingState where
  (==) st1 st2 = (restrictDomain (Set.fromList ["a", "u"]) (_idCount st1) == restrictDomain (Set.fromList ["a", "u"]) (_idCount st2)) &&
                  _typeAssignment st1 == _typeAssignment st2 &&
                  _candidates st1 == _candidates st2

instance Ord TypingState where
  (<=) st1 st2 = (restrictDomain (Set.fromList ["a", "u"]) (_idCount st1) <= restrictDomain (Set.fromList ["a", "u"]) (_idCount st2)) &&
                _typeAssignment st1 <= _typeAssignment st2 &&
                _candidates st1 <= _candidates st2  
  
writeLog level msg = do
  maxLevel <- asks _tcSolverLogLevel
  if level <= maxLevel then traceShow (plain msg) $ return () else return ()
  
