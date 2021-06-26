{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

-- | Incremental solving of subtyping and well-formedness constraints
module Synquid.TypeConstraintSolver (
  ErrorMessage,
  TypingParams (..),
  TypingState,
  typingConstraints,
  typeAssignment,
  qualifierMap,
  hornClauses,
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
  simplifyAllConstraints,
  solveAllCandidates,
  matchConsType,
  hasPotentialScrutinees,
  freshId,
  freshVar,
  freshFromIntersect,
  fresh,
  currentAssignment,
  finalizeType,
  finalizeProgram,
  finalizeWProgram,
  initEnv,
  allScalars,
  condQualsGen,
  topLevelGoals,
  addQuals,
  progressChecks,
  checkProgress,
  addQuals
) where

import Synquid.Logic
import Synquid.Type hiding (set)
import Synquid.Program
import Synquid.Types.Error
import Synquid.Pretty
import Synquid.SolverMonad
import Synquid.Util
import Synquid.Resolver (addAllVariables)
import Synquid.Types.Logic
import Synquid.Types.Program
import Synquid.Types.Type
import Synquid.Types.Params
import Synquid.Types.Explorer
import Synquid.Types.Solver
import Synquid.Types.Rest


import Data.Maybe
import Data.Bifunctor
import Data.Foldable
import Data.List
import Data.List.Extra (allSame, nubOrd)
import Data.Function
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
import Development.Placeholders


-- | 'runTCSolver' @params st go@ : execute a typing computation @go@ with typing parameters @params@ in a typing state @st@
runTCSolver :: TypingParams -> TypingState -> TCSolver s a -> s (Either ErrorMessage (a, TypingState))
runTCSolver params st go = runExceptT $ runReaderT (runStateT go st) params

-- | Initial typing state in the initial environment @env@
initTypingState :: MonadHorn s => Environment -> RSchema -> s TypingState
initTypingState env schema = do
  initCand <- initHornSolver env
  return TypingState {
    _typingConstraints = [],
    _typeAssignment = Map.empty,
    _predAssignment = Map.empty,
    _qualifierMap = Map.empty,
    _candidates = [initCand],
    _initEnv = env,
    _idCount = Map.empty,
    _topLevelGoals = intersectionToList $ toMonotype schema,
    _currentWorldNumOneIdx = -1,
    _isFinal = False,
    _simpleConstraints = [],
    _hornClauses = [],
    _consistencyChecks = [],
    _progressChecks = [],
    _errorContext = (noPos, empty)
  }

-- | Impose typing constraint @c@ on the programs
addTypingConstraint c = over typingConstraints (nubOrd . (c :))

addHornClause c = hornClauses %= (nubOrd . (c :))

-- | Solve @typingConstraints@: either strengthen the current candidates and return shapeless type constraints or fail
solveTypeConstraints :: MonadHorn s => TCSolver s ()
solveTypeConstraints = do
  simplifyAllConstraints

  scs <- use simpleConstraints
  writeLog 3 (text "Simple Constraints" $+$ (vsep $ map pretty scs))

  processAllPredicates
  processAllConstraints
  generateAllHornClauses

  solveHornClauses
  writeLog 2 $ text "Checking progress"
  -- checkProgress
  checkTypeConsistency
  cands <- use candidates
  writeLog 3 $ text "[solveTypeConstraints]: Solved Candidates:" $+$ pretty (cands :: [Candidate])

  hornClauses .= []
  consistencyChecks .= []
  -- progressChecks .= []

{- Implementation -}

-- | Decompose and unify typing constraints;
-- return shapeless type constraints: constraints involving only free type variables, which impose no restrictions yet, but might in the future
simplifyAllConstraints :: MonadHorn s => TCSolver s ()
simplifyAllConstraints = do
  tcs <- use typingConstraints
  writeLog 3 (text "Typing Constraints" $+$ (vsep $ map pretty tcs))
  typingConstraints .= []
  tass <- use typeAssignment
  mapM_ simplifyConstraint tcs

  -- If type assignment has changed, we might be able to process more shapeless constraints:
  tass' <- use typeAssignment
  writeLog 3 (text "Type assignment" $+$ vMapDoc text pretty tass')

  when (Map.size tass' > Map.size tass) simplifyAllConstraints

-- | Assign unknowns to all free predicate variables
processAllPredicates :: MonadHorn s => TCSolver s ()
processAllPredicates = do
  tcs <- use typingConstraints
  typingConstraints .= []
  mapM_ processPredicate tcs

  pass <- use predAssignment
  writeLog 3 (text "Pred assignment" $+$ vMapDoc text pretty pass)

-- | Eliminate type and predicate variables, generate qualifier maps
processAllConstraints :: MonadHorn s => TCSolver s ()
processAllConstraints = do
  tcs <- use simpleConstraints
  simpleConstraints .= []
  mapM_ processConstraint tcs

-- | Convert simple subtyping constraints into horn clauses
generateAllHornClauses :: MonadHorn s => TCSolver s ()
generateAllHornClauses = do
  tcs <- use simpleConstraints
  simpleConstraints .= []
  mapM_ generateHornClauses tcs

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
  let consaxms = instantiateConsAxioms env Nothing
  writeLog 3 $ text "instantiated cons axioms"
  cands' <- lift . lift . lift $ refineCandidates clauses qmap consaxms cands
  writeLog 3 $ text "refinedCandidates"

  when (null cands') (throwError $ text "Cannot find sufficiently strong refinements")
  candidates .= cands'

solveAllCandidates :: MonadHorn s => TCSolver s ()
solveAllCandidates = do
  cands <- use candidates
  cands' <- concat <$> mapM solveCandidate cands
  candidates .= cands'
  where
    solveCandidate c@(Candidate s valids invalids _) =
      if Set.null invalids
        then return [c]
        else do
          qmap <- use qualifierMap
          env <- use initEnv
          cands' <- lift . lift . lift $ refineCandidates [] qmap (instantiateConsAxioms env Nothing) [c]
          concat <$> mapM solveCandidate cands'

-- | Filter out liquid assignments that are too strong for current consistency checks
checkTypeConsistency :: MonadHorn s => TCSolver s ()
checkTypeConsistency = do
  clauses <- use consistencyChecks
  cands <- use candidates
  env <- use initEnv
  cands' <- lift . lift . lift $ checkCandidates Consistency clauses (instantiateConsAxioms env Nothing) cands
  when (null cands') (throwError $ text "Found inconsistent refinements")
  candidates .= cands'

-- | Filter out liquid assignments that do not produce productive conditions
checkProgress :: MonadHorn s => TCSolver s ()
checkProgress = do
  clauses <- use progressChecks
  cands <- use candidates
  env <- use initEnv
  writeLog 2 $ text "Progress checks:" <+> pretty clauses
  cands' <- lift . lift . lift $ checkCandidates Progress clauses (instantiateConsAxioms env Nothing) cands
  when (null cands') (throwError $ text "Found inconsistent refinements") -- TODO: is this still necessary?
  candidates .= cands'


-- | Simplify @c@ into a set of simple and shapeless constraints, possibly extended the current type assignment or predicate assignment
simplifyConstraint :: MonadHorn s => Constraint -> TCSolver s ()
simplifyConstraint c = do
  tass <- use typeAssignment
  pass <- use predAssignment
  simplifyConstraint' tass pass c

-- Any type: drop
simplifyConstraint' :: MonadHorn s => Map Id RType -> Map Id a -> Constraint -> TCSolver s ()
simplifyConstraint' _ _ c@ProductiveCond{} = simpleConstraints %= (c :)
simplifyConstraint' _ _ (Subtype _ _ AnyT _ _) = return ()
simplifyConstraint' _ _ c@(Subtype _ AnyT _ _ _) = return ()
simplifyConstraint' _ _ c@(WellFormed _ AnyT) = return ()
-- Any datatype: drop only if lhs is a datatype
simplifyConstraint' _ _ (Subtype _ (ScalarT (DatatypeT _ _ _) _) t _ _) | t == anyDatatype = return ()
-- simplifyConstraint' _ _ (Subtype _ (ScalarT (TypeVarT _ _) _) t _ _) | t == anyDatatype = return ()
-- Well-formedness of a known predicate drop
simplifyConstraint' _ pass c@(WellFormedPredicate _ _ p) | p `Map.member` pass = return ()

-- Type variable with known assignment: substitute
simplifyConstraint' tass _ (Subtype env tv@(ScalarT (TypeVarT _ a) _) t consistent label) | a `Map.member` tass
  = simplifyConstraint (Subtype env (typeSubstitute tass tv) t consistent label)
simplifyConstraint' tass _ (Subtype env t tv@(ScalarT (TypeVarT _ a) _) consistent label) | a `Map.member` tass
  = simplifyConstraint (Subtype env t (typeSubstitute tass tv) consistent label)
simplifyConstraint' tass _ (WellFormed env tv@(ScalarT (TypeVarT _ a) _)) | a `Map.member` tass
  = simplifyConstraint (WellFormed env (typeSubstitute tass tv))

-- Two unknown free variables: nothing can be done for now
simplifyConstraint' _ _ c@(Subtype env (ScalarT (TypeVarT _ a) _) (ScalarT (TypeVarT _ b) _) _ _) | not (isBound env a) && not (isBound env b)
  = if a == b
      then (error $ show $ text "simplifyConstraint: equal type variables on both sides")
      else ifM (use isFinal)
            (do -- This is a final pass: assign an arbitrary type to one of the variables
              addTypeAssignment a intAll
              simplifyConstraint c)
            (modify $ addTypingConstraint c)
simplifyConstraint' _ _ c@(WellFormed env (ScalarT (TypeVarT _ a) _)) | not (isBound env a)
  = modify $ addTypingConstraint c
simplifyConstraint' _ _ c@(WellFormedPredicate _ _ _) = modify $ addTypingConstraint c

-- Let types: extend environment (has to be done before trying to extend the type assignment)
simplifyConstraint' _ _ (Subtype env (LetT x tDef tBody) t consistent label)
  = simplifyConstraint (Subtype (addVariable x tDef env) tBody t consistent label) -- ToDo: make x unique?
simplifyConstraint' _ _ (Subtype env t (LetT x tDef tBody) consistent label)
  = simplifyConstraint (Subtype (addVariable x tDef env) t tBody consistent label) -- ToDo: make x unique?

-- Unknown free variable and a type: extend type assignment
simplifyConstraint' _ _ c@(Subtype env (ScalarT (TypeVarT _ a) _) t _ _) | not (isBound env a)
  = unify env a t >> simplifyConstraint c
simplifyConstraint' _ _ c@(Subtype env t (ScalarT (TypeVarT _ a) _) _ _) | not (isBound env a)
  = unify env a t >> simplifyConstraint c

-- Compound types: decompose
simplifyConstraint' _ _ (Subtype env (ScalarT (DatatypeT name (tArg:tArgs) pArgs) fml) (ScalarT (DatatypeT name' (tArg':tArgs') pArgs') fml') consistent label)
  = do
      simplifyConstraint (Subtype env tArg tArg' consistent label)
      simplifyConstraint (Subtype env (ScalarT (DatatypeT name tArgs pArgs) fml) (ScalarT (DatatypeT name' tArgs' pArgs') fml') consistent label)
simplifyConstraint' _ _ (Subtype env (ScalarT (DatatypeT name [] (pArg:pArgs)) fml) (ScalarT (DatatypeT name' [] (pArg':pArgs')) fml') consistent label)
  = do
      let variances = _predVariances ((env ^. datatypes) Map.! name)
      let isContra = variances !! (length variances - length pArgs - 1) -- Is pArg contravariant?
      if isContra
        then simplifyConstraint (Subtype env (int $ pArg') (int $ pArg) consistent label)
        else simplifyConstraint (Subtype env (int $ pArg) (int $ pArg') consistent label)
      simplifyConstraint (Subtype env (ScalarT (DatatypeT name [] pArgs) fml) (ScalarT (DatatypeT name' [] pArgs') fml') consistent label)
simplifyConstraint' _ _ (Subtype env (FunctionT x tArg1 tRes1) (FunctionT y tArg2 tRes2) False label)
  = do
      simplifyConstraint (Subtype env tArg2 tArg1 False label)
      if isScalarType tArg1
        then simplifyConstraint (Subtype (addVariable y tArg2 env) (renameVar (isBound env) x y tArg1 tRes1) tRes2 False label)
        else simplifyConstraint (Subtype env tRes1 tRes2 False label)
simplifyConstraint' _ _ (Subtype env (FunctionT x tArg1 tRes1) (FunctionT y tArg2 tRes2) True label)
  = if isScalarType tArg1
      then simplifyConstraint (Subtype (addVariable x tArg1 env) tRes1 tRes2 True label)
      else simplifyConstraint (Subtype env tRes1 tRes2 True label)
simplifyConstraint' _ _ c@(WellFormed env (ScalarT (DatatypeT name tArgs _) fml))
  = do
      mapM_ (simplifyConstraint . WellFormed env) tArgs
      simpleConstraints %= (c :)
simplifyConstraint' _ _ (WellFormed env (FunctionT x tArg tRes))
  = do
      simplifyConstraint (WellFormed env tArg)
      simplifyConstraint (WellFormed (addVariable x tArg env) tRes)
simplifyConstraint' _ _ (WellFormed env (LetT x tDef tBody))
  = simplifyConstraint (WellFormed (addVariable x tDef env) tBody)

-- Simple constraint: return
simplifyConstraint' _ _ c@(Subtype _ (ScalarT baseT _) (ScalarT baseT' _) _ _) | baseT == baseT' = simpleConstraints %= (c :)
simplifyConstraint' _ _ c@(WellFormed _ (ScalarT baseT _)) = simpleConstraints %= (c :)
simplifyConstraint' _ _ c@(WellFormedCond _ _) = simpleConstraints %= (c :)
simplifyConstraint' _ _ c@(WellFormedMatchCond _ _) = simpleConstraints %= (c :)

-- Intersection type
-- RHS: (T <: A; T <: B) ==> T <: A /\ B
simplifyConstraint' _ _ (Subtype env subT superT@(AndT l r) consistent label) =
  do
    simplifyConstraint (Subtype env subT l consistent (label ++ "+l"))
    simplifyConstraint (Subtype env subT r consistent (label ++ "+r"))
-- LHS: A /\ B <: T ... Assert the intersection is a function
simplifyConstraint' _ _ (Subtype env isect@(AndT l r) superT@(FunctionT y superTArg superTRet) consisent@False label) = do
  intersectionStrategy <- asks _tcIntersection
  let conjuncts = intersectionToList isect
  unless (isFunctionType . head $ conjuncts) $
    throwError $ text  "Cannot subtype intersection of non-function" <+> squotes (pretty isect) $+$ text "with " <+> squotes (pretty superT)

  worldIdx <- use currentWorldNumOneIdx
  case intersectionStrategy of
    GuardedPowerset -> do
      conjunctsWithConstraints <- forM conjuncts (\t -> do
        constraintName <- freshId "G"
        logItFrom "Conjunct Guard" $ (text constraintName)
          <+> text "-controls-" <+> pretty t
        let c = Unknown Map.empty constraintName
        -- Set the qualifier map to just False (True is an implicit other option)
        addQuals constraintName (toSpace Nothing [BoolLit False])
        return (t,c))
      let conjunctArgs = map (first argType) conjunctsWithConstraints
      when (any (isIntersection . fst) conjunctArgs) $
        throwError $ text  "Intersection of functions, whose arguments are intersections!" <+> squotes (pretty isect) $+$ text "<(??):" <+> squotes (pretty superT)
      --       cUnknown <- Unknown Map.empty <$> freshId "C"

      -- codomain
      -- Bind the argument in the environement, and generate a new subtyping constraint
      -- G, y: (AndT subTArg1 superTArg), C1 |- [y/x]subTRet <: superTRet
      forM_ (zip conjunctsWithConstraints [1..]) $ \((FunctionT x subTArg subTRet, constraint), idx) -> do
        let env' = addPositiveGuard [constraint] env
        simplifyConstraint $
          Subtype (addVariable y (AndT subTArg superTArg) env')
            (renameVar (isBound env') x y subTArg subTRet)
            superTRet
            consisent (label ++ "+ret-world-" ++ show idx)

      -- TODO: solve what you can rn

      -- domain
      -- Get the powerset of each constraint and its matching constraint
      let jConjuncts = zipWith (\(a,b) c -> (a,b,c)) conjunctArgs [1..] &
                        Set.fromList & Set.powerSet & Set.delete Set.empty & Set.toList &
                        map Set.toList
      forM_ jConjuncts $ \conjunctConstraintSubset -> do
        let (args, inConstraints, worldIdxs) = unzip3 conjunctConstraintSubset
        let worldId = intercalate "," (map show worldIdxs)
        let unionOfArgs = simplifyType $ foldr1 UnionT args
        let outConstraints = map fnot $ filter (`notElem` inConstraints) (map snd conjunctsWithConstraints)
        let env' = addPositiveGuard inConstraints env
        let env'' = addNegativeGuard outConstraints env'
        simplifyConstraint $ Subtype env'' superTArg unionOfArgs consisent (label ++ "+arg-world-union-" ++ worldId)

      -- At least one of the domains needs to be true.
      let (_, constraints) = unzip conjunctArgs
      let atLeastOneConstr = ftrue |=>| (foldr1 (|||) constraints)
      addHornClause (atLeastOneConstr, "at least one")
      return ()

-- Union Type
simplifyConstraint' _ _ c@(Subtype env subT superT@(UnionT l r) consistent label)
  -- Reflexivity
  | l == r  && l == subT = return ()
  -- Union Redundancy
  | allSame (unionToList superT) =
      simplifyConstraint (Subtype env subT (head (unionToList superT)) consistent (label++"+redundant-union"))
  -- If the supertype contains a function then we have to make a choice between them.
  -- Since we got past the Redundancy rule, we know not all functions are the same.
  -- TODO: I'm making an implcit assumption that we'll never union a function and non-function.
  -- It doesn't matter here, but worth noting
  | any isFunctionType $ unionToList superT = makeChoice
  -- Disjuncts are not all the same shape, we have to make a choice.
  | not $ allSame (map baseTypeOf $ unionToList superT) = makeChoice
  -- Each disjunct has the same basetype (i.e., [Bool|True]|len==0 ~ [Bool|True]|len > 0),
  -- we can push the Union into the refinement. But not when the inner types do not match up.
  | allSame (map baseTypeOf $ unionToList superT) = mergeRefinements

  | otherwise = throwError $ text "Cannot decompose RHS union"
    <+> squotes (pretty subT) <+> text "<:"
    <+> squotes (pretty superT) <+> parens (text label)
  where
    makeChoice = do
      intersectionStrategy <- asks _tcIntersection
      case intersectionStrategy of
        GuardedPowerset -> do
          -- All constraints in the environment should be for this current union.
          -- I think.
          -- So force at least one of the constraints to be false.
          -- Generate a horn clause of /\ C => False
          mkHornGuard c env (label ++ "+union-choice-exclusivity")
        _ -> do
          throwError $
            text "Cannot decompose RHS union, at least one has a nested refinement that does not match the rest."
            <+> squotes (pretty subT) <+> text "<:"
            <+> squotes (pretty superT) <+> parens (text label)
    mergeRefinements = do
      $(todo "impossible now that we have added simplifyType")
      let fmls = concatMap allRefinementsOf' $ unionToList superT
      let (ScalarT repB _) = head $ unionToList superT
      let newSuperT = ScalarT repB (foldr1 (|||) fmls)
      simplifyConstraint (Subtype env subT newSuperT consistent (label ++ "+pushed-into-refinement"))
      -- let (posFmls, negFmls) = env ^. subtypeGuards & both Set.toList
      -- forM_ negFmls $ \negFml -> do
      --   let lhsConstraint = foldr1 (|&|) posFmls
      --   let clause = lhsConstraint |=>| (fnot negFml)
      --   let label' = label ++ "+merged-union-exclusivity"
      --   hornClauses %= ((clause, label'):)

-- Otherwise (shape mismatch): fail
simplifyConstraint' _ _ c@(Subtype env t t' _ label)
  | Set.size (fst $ _subtypeGuards env) > 0 = do
    intersectionStrategy <- asks _tcIntersection
    case intersectionStrategy of
      GuardedPowerset -> mkHornGuard c env (label ++ "+shape-exclusivity")
      _ -> defaultCase
  | otherwise = defaultCase
    where
      defaultCase =
        throwError $ text  "Cannot match shape, unresolvable subtype:"
        $+$ squotes (pretty $ shape t) <+> text ":" <+> pretty t
        <+> text "</:" <+> squotes (pretty $ shape t') <+> text ":" <+> pretty t'
        <+> text "from label" <+> squotes (text label)

mkHornGuard c env label = do
  let constraints = env ^. subtypeGuards
  let (posFmls, negFmls) = both Set.toList constraints
  let lhsConstraints = foldr1 (|&|) posFmls
  let rhsConstraints = foldr1 (|||) (defaultList (map (negationNF . fnot) negFmls) ffalse)
  let clause = lhsConstraints |=>| rhsConstraints
  addHornClause (clause, label)
  writeLog 3 $ text "[simplifyConstraint]:" <+> pretty c </> pretty clause <+> parens (text label)

-- | Unify type variable @a@ with type @t@ or fail if @a@ occurs in @t@
unify :: Monad s => Environment -> Id -> TypeSkeleton Formula -> StateT TypingState (ReaderT TypingParams (ExceptT ErrorMessage s)) ()
unify env a t = if a `Set.member` typeVarsOf t
  then error $ show $ text "simplifyConstraint: type variable occurs in the other type"
  else do
    t' <- fresh env t
    writeLog 3 (text "UNIFY" <+> text a <+> text "WITH" <+> pretty t <+> text "PRODUCING" <+> pretty t')
    addTypeAssignment a t'

-- Predicate well-formedness: shapeless or simple depending on type variables
processPredicate c@(WellFormedPredicate env argSorts p) = do
  tass <- use typeAssignment
  let typeVars = Set.toList $ Set.unions $ map typeVarsOfSort argSorts
  if any (isFreeVariable tass) typeVars
    then do
      writeLog 3 $ text "WARNING: free vars in predicate" <+> pretty c
      modify $ addTypingConstraint c -- Still has type variables: cannot determine shape
    else do
      -- u <- freshId "U"
      let u = p
      addPredAssignment p (Unknown Map.empty u)
      let argSorts' = map (sortSubstitute $ asSortSubst tass) argSorts
      let args = zipWith Var argSorts' deBrujns
      let env' = typeSubstituteEnv tass env
      let vars = allScalars env'
      pq <- asks _predQualsGen
      addQuals u (pq (addAllVariables args env') args vars)
  where
    isFreeVariable tass a = not (isBound env a) && not (Map.member a tass)
processPredicate c = modify $ addTypingConstraint c

-- | Eliminate type and predicate variables from simple constraints, create qualifier maps, split measure-based subtyping constraints
processConstraint :: MonadHorn s => Constraint -> TCSolver s ()
processConstraint c@(Subtype env (ScalarT baseTL l) (ScalarT baseTR r) False label) | baseTL == baseTR
  = if l == ffalse || r == ftrue
      then return ()
      else do
        tass <- use typeAssignment
        pass <- use predAssignment
        let subst = sortSubstituteFml (asSortSubst tass) . substitutePredicate pass
        let l' = subst l
        let r' = subst r
        let c' = Subtype env (ScalarT baseTL l') (ScalarT baseTR r') False label
        if Set.null $ (predsOf l' `Set.union` predsOf r') Set.\\ (Map.keysSet $ allPredicates env)
            then case baseTL of -- Subtyping of datatypes: try splitting into individual constraints between measures
                  DatatypeT dtName _ _ -> do
                    let measures = Map.keysSet $ allMeasuresOf dtName env
                    let isAbstract = null $ ((env ^. datatypes) Map.! dtName) ^. constructors
                    let vals = filter (\v -> varName v == valueVarName) . Set.toList . varsOf $ r'
                    let rConjuncts = conjunctsOf r'
                    doSplit <- asks _tcSolverSplitMeasures
                    if not doSplit || isAbstract || null vals || (not . Set.null . unknownsOf) (l' |&| r') -- TODO: unknowns can be split if we know their potential valuations
                      then simpleConstraints %= (c' :) -- Constraint has unknowns (or RHS doesn't contain _v)
                      else case splitByPredicate measures (head vals) (Set.toList rConjuncts) of
                            Nothing -> simpleConstraints %= (c' :) -- RHS cannot be split, add whole thing
                            Just mr -> if rConjuncts `Set.isSubsetOf` (Set.unions $ Map.elems mr)
                                        then do
                                          let lConjuncts = conjunctsOf $ instantiateCons (head vals) l'
                                          case splitByPredicate measures (head vals) (Set.toList lConjuncts) of -- Every conjunct of RHS is about some `m _v` (where m in measures)
                                              Nothing -> simpleConstraints %= (c' :) -- LHS cannot be split, add whole thing for now
                                              Just ml -> mapM_ (addSplitConstraint ml) (toDisjointGroups mr)
                                        else simpleConstraints %= (c' :) -- Some conjuncts of RHS are no covered (that is, do not contains _v), add whole thing
                  _ -> simpleConstraints %= (c' :)
          else modify $ addTypingConstraint c -- Constraint contains free predicate: add back and wait until more type variables get unified, so predicate variables can be instantiated
  where
    instantiateCons val fml@(Binary Eq v (Cons _ _ _)) | v == val = conjunction $ instantiateConsAxioms env (Just val) fml
    instantiateCons _ fml = fml

    addSplitConstraint :: MonadHorn s => Map Id (Set Formula) -> (Set Id, Set Formula) -> TCSolver s ()
    addSplitConstraint ml (measures, rConjuncts) = do
      let rhs = conjunction rConjuncts
      let lhs = conjunction $ setConcatMap (\measure -> Map.findWithDefault Set.empty measure ml) measures
      let c' = Subtype env (ScalarT baseTL lhs) (ScalarT baseTR rhs) False label
      writeLog 3 $ text "addSplitConstraint" <+> pretty c'
      simpleConstraints %= (c' :)

processConstraint (Subtype env (ScalarT baseTL l) (ScalarT baseTR r) True label) | baseTL == baseTR
  = do
      tass <- use typeAssignment
      pass <- use predAssignment
      let subst = sortSubstituteFml (asSortSubst tass) . substitutePredicate pass
      let l' = subst l
      let r' = subst r
      if l' == ftrue || r' == ftrue
        then return ()
        else simpleConstraints %= (Subtype env (ScalarT baseTL l') (ScalarT baseTR r') True label :)
processConstraint (WellFormed env t@(ScalarT baseT fml))
  = case fml of
      Unknown _ u -> do
        qmap <- use qualifierMap
        tass <- use typeAssignment
        tq <- asks _typeQualsGen
        -- Only add qualifiers if it's a new variable; multiple well-formedness constraints could have been added for constructors
        let env' = typeSubstituteEnv tass env
        let env'' = addVariable valueVarName t env'
        unless (Map.member u qmap) $ addQuals u (tq env'' (Var (toSort baseT) valueVarName) (allScalars env'))
      _ -> return ()
processConstraint (WellFormedCond env (Unknown _ u))
  = do
      tass <- use typeAssignment
      cq <- asks _condQualsGen
      let env' = typeSubstituteEnv tass env
      addQuals u (cq env' (allScalars env'))
processConstraint (WellFormedMatchCond env (Unknown _ u))
  = do
      tass <- use typeAssignment
      mq <- asks _matchQualsGen
      let env' = typeSubstituteEnv tass env
      addQuals u (mq env' (allPotentialScrutinees env'))
processConstraint (ProductiveCond envs c) = do
  tass <- use typeAssignment
  pass <- use predAssignment
  let c' = substitute pass c
  let subst = sortSubstituteFml (asSortSubst tass) . substitutePredicate pass
  simpleConstraints %= (ProductiveCond envs c' :)

processConstraint c = error $ show $ text "processConstraint: not a simple constraint" <+> pretty c

generateHornClauses :: MonadHorn s => Constraint -> TCSolver s ()
generateHornClauses c@(Subtype env (ScalarT baseTL l) (ScalarT baseTR r) False label) | baseTL == baseTR
  = do
      qmap <- use qualifierMap
      let relevantVars = potentialVars qmap (l |&| r)
      emb <- embedding env relevantVars baseTL True
      let negGuards = (env ^. subtypeGuards) & snd & Set.map (negationNF . fnot)
      clauses <- lift . lift . lift $ preprocessConstraint (conjunction (Set.insert l emb) |=>| (foldr (|||) r negGuards))
      hornClauses %= (nubOrd . (zip clauses (repeat label) ++))
generateHornClauses (Subtype env (ScalarT baseTL l) (ScalarT baseTR r) True _) | baseTL == baseTR
  = do
      qmap <- use qualifierMap
      let relevantVars = potentialVars qmap (l |&| r)
      emb <- embedding env relevantVars baseTL False
      let guards = (env ^. subtypeGuards) & uncurry Set.union
      let rhs = conjunction (Set.insert l $ Set.insert r emb)
      let lhs = conjunction guards
      consistencyChecks %= ((lhs |=>| rhs) :)
generateHornClauses (ProductiveCond envs c) = do
  qmap <- use qualifierMap
  let relevantVars = potentialVars qmap c
  embs <- mapM (\e -> conjunction <$> embedding e relevantVars BoolT True) envs -- Base type shouldn't matter as long as it isn't a datatype
  let mkFml e = e |&| c
  -- This isn't actually a horn clause but whatever
  let hc = disjunction $ map mkFml embs
  progressChecks %= (hc :)
generateHornClauses c = error $ show $ text "generateHornClauses: not a simple subtyping constraint" <+> pretty c

-- | 'allScalars' @env@ : logic terms for all scalar symbols in @env@
allScalars :: Environment -> [Formula]
allScalars env = mapMaybe toFormula $ Map.toList $ symbolsOfArity 0 env
  where
    toFormula (_, ForallT _ _) = Nothing
    toFormula (x, _) | x `Set.member` (env ^. letBound) = Nothing
    toFormula (x, Monotype t) = case t of
      ScalarT IntT  (Binary Eq _ (IntLit n)) -> Just $ IntLit n
      ScalarT BoolT (Var _ _) -> Just $ BoolLit True
      ScalarT BoolT (Unary Not (Var _ _)) -> Just $ BoolLit False
      ScalarT (DatatypeT dt [] []) (Binary Eq _ cons@(Cons _ name [])) | x == name -> Just cons
      ScalarT b _ -> Just $ Var (toSort b) x
      _ -> Nothing

-- | 'allPotentialScrutinees' @env@ : logic terms for all scalar symbols in @env@
allPotentialScrutinees :: Environment -> [Formula]
allPotentialScrutinees env = mapMaybe toFormula $ Map.toList $ symbolsOfArity 0 env
  where
    toFormula (x, Monotype t) = case t of
      ScalarT b@(DatatypeT _ _ _) _ ->
        if Set.member x (env ^. unfoldedVars) && (Program (PSymbol x) [] `notElem` (env ^. usedScrutinees))
          then Just $ Var (toSort b) x
          else Nothing
      _ -> Nothing
    toFormula _ = Nothing

hasPotentialScrutinees :: Monad s => Environment -> TCSolver s Bool
hasPotentialScrutinees env = do
  tass <- use typeAssignment
  return $ not $ null $ allPotentialScrutinees (typeSubstituteEnv tass env)

-- | Assumptions encoded in an environment
embedding :: Monad s => Environment -> Set Id -> BaseType Formula -> Bool -> TCSolver s (Set Formula)
embedding env vars vvBase includeQuantified = do
    tass <- use typeAssignment
    pass <- use predAssignment
    qmap <- use qualifierMap
    let posGuards = env ^. subtypeGuards & fst
    let ass = Set.map (substitutePredicate pass) (env ^. assumptions)
    let allVars = vars `Set.union` potentialVars qmap (conjunction ass)
    let bindings = addBindings env tass pass qmap (Set.union ass posGuards) allVars
    return bindings
  where
    addBindings env tass pass qmap fmls vars =
      if Set.null vars
        then fmls
        else let (x, rest) = Set.deleteFindMin vars
              in
              case Map.lookup x (allSymbols env) of
                Nothing ->
                  let posts = Set.fromList $ if x == valueVarName
                        then allMeasurePostconditions includeQuantified vvBase env
                        else []
                   in addBindings env tass pass qmap (posts `Set.union` fmls) rest -- Variable not found (useful to ignore value variables)
                Just (Monotype t) -> case typeSubstitute tass t of
                  ScalarT baseT fml -> let
                    fmls' = Set.fromList $ map (substitute (Map.singleton valueVarName (Var (toSort baseT) x)) . substitutePredicate pass)
                                          (fml : allMeasurePostconditions includeQuantified baseT env)
                    newFmls = Set.difference fmls' fmls
                    newVars = Set.delete x $ setConcatMap (potentialVars qmap) newFmls
                    in
                    addBindings env tass pass qmap (fmls `Set.union` newFmls) (rest `Set.union` newVars)
                  LetT y tDef tBody -> addBindings (addVariable x tBody . addVariable y tDef . removeVariable x $ env) tass pass qmap fmls vars
                  AnyT -> Set.singleton ffalse
                  AndT l r -> let
                    envl = addVariable x l (removeVariable x env)
                    envr = addVariable x r (removeVariable x env)
                    leftBound = addBindings envl tass pass qmap fmls (Set.singleton x)
                    rightBound = addBindings envr tass pass qmap fmls vars
                    in
                      leftBound `Set.union` rightBound
                  t -> error $ unwords ["embedding: encountered non-scalar variable", x, "in 0-arity bucket, with type", show $ pretty t]
                Just sch -> addBindings env tass pass qmap fmls rest -- TODO: why did this work before?
    allSymbols = symbolsOfArity 0

bottomValuation :: QMap -> Formula -> Formula
bottomValuation qmap fml = applySolution bottomSolution fml
  where
    unknowns = Set.toList $ unknownsOf fml
    bottomSolution = Map.fromList $ zip (map unknownName unknowns) (map (Set.fromList . lookupQualsSubst qmap) unknowns)

-- | 'potentialVars' @qmap fml@ : variables of @fml@ if all unknowns get strongest valuation according to @quals@
potentialVars :: QMap -> Formula -> Set Id
potentialVars qmap fml = Set.map varName $ varsOf $ bottomValuation qmap fml

-- | 'freshId' @prefix@ : fresh identifier starting with @prefix@
freshId :: Monad s => String -> TCSolver s String
freshId prefix = do
  i <- uses idCount (Map.findWithDefault 1 prefix)
  idCount %= Map.insert prefix (i + 1)
  return $ prefix ++ show i

freshVar :: Monad s => Environment -> String -> TCSolver s String
freshVar env prefix = do
  x <- freshId prefix
  if Map.member x (allSymbols env)
    then freshVar env prefix
    else return x

-- | 'somewhatFreshVar' @env prefix sort@ : A variable of sort @sort@ not bound in @env@
-- Exists to generate fresh variables for multi-argument measures without making all of the constructor axiom instantiation code monadic
somewhatFreshVar :: Environment -> String -> Sort -> Formula
somewhatFreshVar env prefix s = Var s name
  where
    name = unbound 0 (prefix ++ show 0)
    unbound n v = if Map.member v (allSymbols env)
                    then unbound (n + 1) (v ++ show n)
                    else v

-- | 'fresh' @t@ : a type with the same shape as @t@ but fresh type variables,
-- fresh predicate variables, and fresh unknowns as refinements.
-- a "fresh" intersection is not an intersection, but has the shape of one of its conjuncts
fresh :: Monad s => Environment -> RType -> TCSolver s RType
fresh env (ScalarT (TypeVarT vSubst a) _) | not (isBound env a) = do
  -- Free type variable: replace with fresh free type variable
  a' <- freshId "A"
  return $ ScalarT (TypeVarT vSubst a') ftrue
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
      let (DatatypeDef tParams pParams _ _ _) = (env ^. datatypes) Map.! name
      pArgs' <- mapM (\sig -> freshPred env . map (noncaptureSortSubst tParams (map (toSort . baseTypeOf) tArgs')) . predSigArgSorts $ sig) pParams
      return $ DatatypeT name tArgs' pArgs'
    freshBase baseT = return baseT
fresh env (FunctionT x tArg tFun) =
  liftM2 (FunctionT x) (fresh env tArg) (fresh env tFun)
-- fresh env (AndT l r) = fresh env (fst $ antiUnify' ftrue l r Map.empty)
fresh env t =  let (env', t') = embedContext env t in fresh env' t'

freshPred env sorts = do
  p' <- freshId "P"
  modify $ addTypingConstraint (WellFormedPredicate env sorts p')
  let args = zipWith Var sorts deBrujns
  return $ Pred BoolS p' args

-- Get a fresh, non-intersection type. When the intersection has many different
-- shapes in it, produce a fresh type matching some goal shape.
freshFromIntersect env t@(AndT l r) goalType = do
  let goalShapes = intersectionToList t & filter (on arrowEq shape goalType)
  case listToMaybe goalShapes of
    Nothing -> error $ "Specification has a shape mismatch. Nothing matches:\n" ++
        show (plain $ pretty (shape goalType)) ++ "\nfrom:\n" ++
        show (plain $ pretty $ map shape $ intersectionToList t)
    Just t' -> fresh env t'
freshFromIntersect env (FunctionT x tArg tRes) (FunctionT gx goalArg goalRes) = do
  tArg' <- freshFromIntersect env tArg goalArg
  tRes' <- freshFromIntersect env tRes goalRes
  return $ FunctionT x tArg' tRes'
freshFromIntersect env t@(ScalarT _ _) goalType = fresh env t

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
setUnknownRecheck :: MonadHorn s => Id -> Set Formula -> Set Id -> TCSolver s ()
setUnknownRecheck name valuation duals = do
  writeLog 3 $ text "Re-checking candidates after updating" <+> text name
  cands <- use candidates
  let cand = head cands
  let clauses = Set.filter (\fml -> name `Set.member` (Set.map unknownName (unknownsOf fml))) (validConstraints cand) -- First candidate cannot have invalid constraints
  let cands' = map (\c -> c { solution = Map.insert name valuation (solution c) }) cands
  env <- use initEnv
  cands'' <- lift . lift . lift $ checkCandidates Validity (Set.toList clauses) (instantiateConsAxioms env Nothing) cands'

  if null cands''
    then throwError $ text "Re-checking candidates failed"
    else do
      let liveClauses = Set.filter (\fml -> duals `disjoint` (Set.map unknownName (unknownsOf fml))) (validConstraints cand)
      candidates .= map (\c -> c {
                                  validConstraints = Set.intersection liveClauses (validConstraints c),
                                  invalidConstraints = Set.intersection liveClauses (invalidConstraints c) }) cands'' -- Remove Horn clauses produced by now eliminated code

-- | 'instantiateConsAxioms' @env fml@ : If @fml@ contains constructor applications, return the set of instantiations of constructor axioms for those applications in the environment @env@
instantiateConsAxioms :: Environment -> Maybe Formula -> Formula -> Set Formula
instantiateConsAxioms env mVal fml = let inst = instantiateConsAxioms env mVal in
  case fml of
    Cons resS@(DataS dtName _) ctor args -> Set.unions $ Set.fromList (map (measureAxiom resS ctor args) (Map.assocs $ allMeasuresOf dtName env)) :
                                                         map (instantiateConsAxioms env Nothing) args
    Unary op e -> inst e
    Binary op e1 e2 -> inst e1 `Set.union` inst e2
    Ite e0 e1 e2 -> inst e0 `Set.union` inst e1 `Set.union` inst e2
    SetLit _ elems -> Set.unions (map inst elems)
    Pred _ p args -> Set.unions $ map inst args
    _ -> Set.empty
  where
    measureAxiom resS ctor args (mname, MeasureDef inSort _ defs constantArgs _) =
      let
        MeasureCase _ vars body = head $ filter (\(MeasureCase c _ _) -> c == ctor) defs
        sParams = map varSortName (sortArgsOf inSort) -- sort parameters in the datatype declaration
        sArgs = sortArgsOf resS -- actual sort argument in the constructor application
        body' = noncaptureSortSubstFml sParams sArgs body -- measure definition with actual sorts for all subexpressions
        newValue = fromMaybe (Cons resS ctor args) mVal
        subst = Map.fromList $ (valueVarName, newValue) : zip vars args
        -- Body of measure with constructor application (newValue) substituted for _v:
        vSubstBody = substitute subst body'
      in foldr (\(x,s) fml -> All (Var s x) fml) vSubstBody constantArgs -- quantify over all the extra arguments of the measure

-- | 'matchConsType' @formal@ @actual@ : unify constructor return type @formal@ with @actual@
matchConsType formal@(ScalarT (DatatypeT d vars pVars) _) actual@(ScalarT (DatatypeT d' args pArgs) _) | d == d'
  = do
      writeLog 3 $ text "Matching constructor type" $+$ pretty formal $+$ text "with scrutinee" $+$ pretty actual
      zipWithM_ (\(ScalarT (TypeVarT _ a) (BoolLit True)) t -> addTypeAssignment a t) vars args
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


-- foo :: Monad s => RProgram -> TCSolver s RProgram
finalizeWProgram :: Monad s => RWProgram -> TCSolver s RWProgram
finalizeWProgram p = do
  tass <- use typeAssignment
  pass <- use predAssignment
  sol <- uses candidates (solution . head)
  return $ fmap (map (typeApplySolution sol . typeSubstitutePred pass . typeSubstitute tass)) p

writeLog level msg = do
  maxLevel <- asks _tcSolverLogLevel
  when (level <= maxLevel) $ traceShow (plain msg) (return ())

logItFrom fnName msg = do
  writeLog 1 $ brackets (text fnName) <+> msg