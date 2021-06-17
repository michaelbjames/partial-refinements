{-# LANGUAGE TemplateHaskell, FlexibleContexts, TupleSections, DeriveDataTypeable #-}

-- | Generating synthesis constraints from specifications, qualifiers, and program templates
module Synquid.Explorer where

import Synquid.Logic
import Synquid.Type hiding (set)
import Synquid.Program
import Synquid.Types.Error
import Synquid.SolverMonad
import Synquid.TypeConstraintSolver hiding (freshId, freshVar, fresh, freshFromIntersect)
import qualified Synquid.TypeConstraintSolver as TCSolver
import Synquid.Util
import Synquid.Pretty
import Synquid.Tokens
import Synquid.Types.Logic
import Synquid.Types.Program
import Synquid.Types.Type
import Synquid.Types.Rest
import Synquid.Types.Explorer
import Synquid.Types.Params

import Data.Bifunctor
import Data.Maybe
import Data.List
import Data.List.Extra (allSame, nubOrd, nubOrdOn)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Char
import Control.Monad.Logic
import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative hiding (empty)
import Control.Lens
import Debug.Trace
import Development.Placeholders
import Data.Data (Data)
import qualified Text.PrettyPrint.ANSI.Leijen as L


-- | 'runExplorer' @eParams tParams initTS go@ : execute exploration @go@ with explorer parameters @eParams@, typing parameters @tParams@ in typing state @initTS@
runExplorer :: (Pretty a, MonadHorn s) => ExplorerParams -> TypingParams -> Reconstructor s -> TypingState -> Explorer s a -> s (Either ErrorMessage a)
runExplorer eParams tParams topLevel initTS go = do
    (ress, PersistentState _ _ errs) <- runStateT
      (observeManyT 1 $ runReaderT (evalStateT go initExplorerState)
        (eParams, tParams, topLevel))
      (PersistentState Map.empty Map.empty [])
    case ress of
        [] ->
            case errs of
                [] -> return $ Left impossible
                -- all logged errors are in es. The error for the last program tried is the head.
                (e : es) -> return $ Left e
        (res : _) -> return $ Right res
  where
    initExplorerState = ExplorerState initTS [] Map.empty Map.empty Map.empty
    impossible =
        ErrorMessage
            { emKind = SynthesisError
            , emPosition = _sourcePos eParams
            , emDescription = text "Synthesis goal is impossible: components or search parameters are insufficient."
            }

-- | 'generateI' @env t@ : explore all terms that have refined type @t@ in environment @env@
-- (top-down phase of bidirectional typechecking)
generateI :: MonadHorn s => [World] -> Explorer s RWProgram
generateI envTy@((env, FunctionT{}):_) = do
  let ts = map snd envTy
  unless (all isFunctionType ts) (error "generateI, not all functions")
  unless (allSame $ map argName ts) (error "the intersected functions don't all use the same arg name! They should.")
  let x = argName $ head ts
  let ctx = \p -> Program (PFun x p) ts
  let tRess = map resType ts
  let worlds' = map (\(env, FunctionT x tArg tRes) -> (unfoldAllVariables $ addVariable x tArg env, tRes)) envTy
  pBody <- inContext ctx $ generateI worlds'
  return $ ctx pBody
generateI envTy@[(env, AndT{})] = do
  let flattenTypes = concatMap (intersectionToList . snd) envTy
  let newWorlds = map (env,) flattenTypes
  generateI newWorlds
generateI ws@((env, ScalarT{}):_) = do
    let ts = map snd ws
    unless (all isScalarType ts) (error "generateI, not scalars")
    maEnabled <- asks . view $ _1 . abduceScrutinees -- Is match abduction enabled?
    d <- asks . view $ _1 . matchDepth
    maPossible <- runInSolver $ hasPotentialScrutinees env -- Are there any potential scrutinees in scope?
    logItFrom "generateI-ScalarT" $ text "are there scrutinees?" <+> pretty maPossible
    if maEnabled && d > 0 && maPossible then generateMaybeMatchIf ws else generateMaybeIf ws
generateI _ = error "impossible"

-- | Generate a possibly conditional term type @t@, depending on whether a condition is abduced
generateMaybeIf :: MonadHorn s => [World] -> Explorer s RWProgram
generateMaybeIf ws = ifte generateThen (uncurry $ generateElse ws) (generateMatch ws) -- If at least one solution without a match exists, go with it and continue with the else branch; otherwise try to match
  where
--     -- | Guess an E-term and abduce a condition for it
    generateThen = do
        envAndcUnknowns <- forM ws $ \(env, t) -> do
            constrName <- freshId "C"
            let cUnknown = Unknown Map.empty constrName
            runInSolver $ TCSolver.addQuals constrName (toSpace Nothing [BoolLit False])

            logItFrom "generateThen" $ text "cUnknown:" <+> pretty cUnknown <+> text "for type" <+> pretty t
            addConstraint $ WellFormedCond env cUnknown
            return (addAssumption cUnknown env, cUnknown)
        let (envs', cUnknowns) = unzip envAndcUnknowns
        let ws' = zip envs' (map snd ws)
        logItFrom "generateThen" $ text "got constraint worlds, finding a then in:" </> pretty ws'
        -- TODO: Consider using atLeastOneWorld here.
        pThen <-  cut (generateE ws') -- Do not backtrack: if we managed to find a solution for a nonempty subset of inputs, we go with it
        logItFrom "generateThen" $ text "then found:" <+> pretty pThen
        conds <- forM cUnknowns (\cUnknown -> conjunction <$> currentValuation cUnknown)
        return (conds, pThen)

-- | Proceed after solution @pThen@ has been found under assumption @cond@
generateElse :: MonadHorn s => [World] -> [Formula] -> RWProgram -> Explorer s RWProgram
generateElse ws conds pThen = if all (== ftrue) conds
    then do
      logItFrom "generateElse" $ text "then conditions all True, no need for ite."
      return pThen -- @pThen@ is valid under no assumptions, in all worlds: return it
    else do -- @pThen@ is valid under a nontrivial assumption, proceed to look for the solution for the rest of the inputs
        logItFrom "generateElse" $ text "must find a conditional expression."
        pCond <- inContext (\p -> Program (PIf p uHoleWorld uHoleWorld ) ts) $ generateCondition envs conds

        cUnknowns <- replicateM (length ws) $ Unknown Map.empty <$> freshId "C"
        runInSolver $ forM_ (zip conds cUnknowns) $ \(cond, cUnknown) -> do
            addFixedUnknown (unknownName cUnknown) (Set.singleton $ fnot cond) -- Create a fixed-valuation unknown to assume @!cond@
        let envs' = zipWith addAssumption cUnknowns envs
        let ws' = zip envs' ts
        pElse <- optionalInPartial ts $ inContext (\p -> Program (PIf pCond pThen p) ts) $ generateI ws'
        return $ Program (PIf pCond pThen pElse) ts
        {- ifM (tryEliminateBranching pElse (runInSolver $ setUnknownRecheck (unknownName cUnknown) Set.empty (Set.singleton condUnknown)))
        (return pElse)
        (return $ Program (PIf pCond pThen pElse) t)
        -}
    where
        (envs, ts) = unzip ws

tryEliminateBranching branch recheck =
  if isHole branch
      then return False
      else ifte -- If synthesis of the branch succeeded, try to remove the branching construct
            recheck -- Re-check Horn constraints after retracting the branch guard
            (const $ return True) -- constraints still hold: @branch@ is a valid solution overall
            (return False) -- constraints don't hold: the guard is essential

generateCondition :: MonadHorn s => [Environment] -> [Formula] -> Explorer s RWProgram
generateCondition envs fmls = do
    conjuncts <- mapM genConjunct allConjunctsPerWorld
    return $ fmap (\ts -> zipWith (\t fml -> addRefinement t (valBool |=| fml)) ts fmls)
      (foldl1 conjoin conjuncts)
    where
        allConjunctsPerWorld = map (Set.toList . conjunctsOf) fmls
        genConjunct cs = if all isExecutable cs
            then let pgms = map fmlToProgram cs
                in if not (allSame pgms)
                    then generateError envs
                    else return $ joinPrograms pgms
            else do
              let worlds =  zip envs (map (\c -> ScalarT BoolT $ valBool |=| c) cs)
              cut (generateE worlds)
        andSymb = Program (PSymbol $ binOpTokens Map.! And) (replicate (length envs) $ toMonotype $ binOpType And)
        conjoin p1 p2 = Program (PApp (Program (PApp andSymb p1) (replicate (length envs) boolAll)) p2) (replicate (length envs) boolAll)

-- | If partial solutions are accepted, try @gen@, and if it fails, just leave a hole of type @t@; otherwise @gen@
optionalInPartial :: MonadHorn s => t -> Explorer s (Program t) -> Explorer s (Program t)
optionalInPartial t gen = ifM (asks . view $ _1 . partialSolution) (ifte gen return (return $ Program PHole t)) gen

-- | Generate a match term of type @t@
generateMatch :: MonadHorn s => [World] -> Explorer s RWProgram
generateMatch ws = do
    d <- asks . view $ _1 . matchDepth
    if d == 0
        then mzero
        else do
        (Program p tScrs) <- local (over _1 (\params -> set eGuessDepth (view scrutineeDepth params) params))
                        $ inContext (\p -> Program (PMatch p []) ts)
                        $ generateE (zip envs (replicate (length envs) anyDatatype)) -- Generate a scrutinee of an arbitrary type
        let (envs', tScrs') = unzip $ zipWith embedContext envs tScrs
        let pScrutinee = Program p tScrs'

        guard (all typeIsData tScrs')
        case head tScrs' of
            (ScalarT (DatatypeT scrDT _ _) _) -> do -- Type of the scrutinee is a datatype
                let sampleEnv = head envs'
                let ctors = ((sampleEnv ^. datatypes) Map.! scrDT) ^. constructors

                let scrutineeSymbols = symbolList pScrutinee
                let isGoodScrutinee env = not (null ctors) &&                                               -- Datatype is not abstract
                                        not (pScrutinee `elem` (env ^. usedScrutinees)) &&              -- Hasn't been scrutinized yet
                                        not (head scrutineeSymbols `elem` ctors) &&                     -- Is not a value
                                        any (not . flip Set.member (env ^. constants)) scrutineeSymbols -- Has variables (not just constants)
                guard $ all isGoodScrutinee envs'

                (envs'', xs) <- toVar (map (addScrutinee pScrutinee) envs') pScrutinee
                (pCase, conds, condUnknown) <- cut $ generateFirstCase envs'' xs pScrutinee ts (head ctors)                  -- First case generated separately in an attempt to abduce a condition for the whole match
                let envsWithAssumption = zipWith addAssumption conds envs''
                pCases <- map fst <$> mapM (cut . generateCase envsWithAssumption xs pScrutinee ts) (tail ctors)  -- Generate a case for each of the remaining constructors under the assumption
                let pThen = Program (PMatch pScrutinee (pCase : pCases)) ts
                generateElse ws conds pThen                                                               -- Generate the else branch
            _ -> error "impossible"
    where
        (envs, ts) = unzip ws

generateFirstCase :: MonadHorn s => [Environment] -> [Formula] -> RWProgram -> TypeVector -> Id -> Explorer s (Case TypeVector, [Formula], Id)
-- generateFirstCase = $(todo "generateFirstCase")
generateFirstCase envs scrVars pScrutinee ts consName = do
  case Map.lookup consName (allSymbols $ head envs) of
    Nothing -> error $ show $ text "Datatype constructor" <+> text consName <+> text "not found in the environment" <+> pretty (head envs)
    Just consSch -> do
        consTs <- mapM (\env -> instantiate env consSch True []) envs
        -- Each world matches the return of the constructor
        zipWithM_ (\consT tScr -> runInSolver $ matchConsType (lastType consT) tScr) consTs (typeOf pScrutinee)
        -- assignments for the constructor in each world.
        consTs' <- mapM (runInSolver . currentAssignment) consTs
        binders <- replicateM (arity $ head consTs') (freshVar (head envs) "x")
        (symsPerWorld, assPerWorld) <- unzip <$> (sequence $ zipWith4 caseSymbols envs scrVars (replicate (length envs) binders) consTs')
        let caseEnvs = zipWith3 (\ass env syms -> foldr (uncurry addVariable) (addAssumption ass env) syms) assPerWorld envs symsPerWorld

        ifte  (do -- Try to find a vacuousness condition:
                deadUnknown <- Unknown Map.empty <$> freshId "C"
                forM_ envs $ \env -> addConstraint $ WellFormedCond env deadUnknown
                err <- inContext (\p -> Program (PMatch pScrutinee [Case consName binders p]) ts) $ generateError (map (addAssumption deadUnknown) caseEnvs)
                deadValuation <- conjunction <$> currentValuation deadUnknown
                ifte (generateError (map (addAssumption deadValuation) envs)) (const mzero) (return ()) -- The error must be possible only in this case
                return (err, (replicate (length envs) deadValuation), unknownName deadUnknown))
                (\(err, deadCond, deadUnknown) -> return $ (Case consName binders err, deadCond, deadUnknown))
                (do
                    let caseWorlds = zip caseEnvs ts
                    pCaseExpr <- local (over (_1 . matchDepth) (-1 +))
                                    $ inContext (\p -> Program (PMatch pScrutinee [Case consName binders p]) ts)
                                    $ generateI caseWorlds
                    return $ (Case consName binders pCaseExpr, replicate (length envs) ftrue, dontCare))

-- | Generate the @consName@ case of a match term with scrutinee variable @scrName@ and scrutinee type @scrType@
generateCase :: MonadHorn s => [Environment] -> [Formula] -> RWProgram -> TypeVector -> Id -> Explorer s (Case TypeVector, Explorer s ())
-- generateCase = $(todo "generateCase")
generateCase envs scrVars pScrutinee scrTypes consName = do
    case Map.lookup consName (allSymbols (head envs)) of
        Nothing -> error $ show $ text "Datatype constructor" <+> text consName <+> text "not found in the environment" <+> pretty (head envs)
        Just consSch -> do
            consTs <- forM envs $ \env -> instantiate env consSch True []
            zipWithM_ (\lastConsT pScrTy -> runInSolver $ matchConsType lastConsT pScrTy) (map lastType consTs) (typeOf pScrutinee)
            consTs' <- forM consTs $ \consT -> runInSolver $ currentAssignment consT
            binders <- replicateM (arity (head consTs')) (freshVar (head envs) "x")
            (symsPerWorld, assPerWorld) <- unzip <$> sequence (zipWith4 caseSymbols envs scrVars (replicate (length envs) binders) consTs')
            unfoldSyms <- asks . view $ _1 . unfoldLocals

            cUnknown <- Unknown Map.empty <$> freshId "M"
            forM_ assPerWorld $ \ass -> runInSolver $ addFixedUnknown (unknownName cUnknown) (Set.singleton ass) -- Create a fixed-valuation unknown to assume @ass@
            let caseEnvs = zipWith (\env syms -> (if unfoldSyms then unfoldAllVariables else id) $
                            foldr (uncurry addVariable) (addAssumption cUnknown env) syms) envs symsPerWorld
            pCaseExpr <-
                optionalInPartial scrTypes $
                    local (over (_1 . matchDepth) (-1 +)) $
                        inContext (\p -> Program (PMatch pScrutinee [Case consName binders p]) scrTypes) $
                            generateError caseEnvs `mplus` generateI (zip caseEnvs scrTypes)

            let recheck =
                    if disjoint (symbolsOf pCaseExpr) (Set.fromList binders)
                        then runInSolver $ setUnknownRecheck (unknownName cUnknown) Set.empty Set.empty -- ToDo: provide duals here
                        else mzero

            return (Case consName binders pCaseExpr, recheck)

-- | 'caseSymbols' @scrutinee binders consT@: a pair that contains (1) a list of bindings of @binders@ to argument types of @consT@
-- and (2) a formula that is the return type of @consT@ applied to @scrutinee@
caseSymbols env x [] (ScalarT _ fml) = let subst = substitute (Map.singleton valueVarName x) in
  return ([], subst fml)
caseSymbols env x (name : names) (FunctionT y tArg tRes) = do
  (syms, ass) <- caseSymbols env x names (renameVar (isBound env) y name tArg tRes)
  return ((name, tArg) : syms, ass)

-- | Generate a possibly conditional possibly match term, depending on which conditions are abduced
generateMaybeMatchIf :: MonadHorn s => [World] -> Explorer s RWProgram
-- generateMaybeMatchIf ws = $(todo "generateMaybeMatchIf with worlds")
generateMaybeMatchIf ws = (generateOneBranch >>= generateOtherBranches) `mplus` (generateMatch ws) -- might need to backtrack a successful match due to match depth limitation
  where
    (envs, ts) = unzip ws

    -- generateOneBranch :: MonadHorn s => Explorer s ([[Formula]], [Formula], RWProgram)
    generateOneBranch = do
        matchUnknown <- Unknown Map.empty <$> freshId "M"
        forM_ envs $ \env -> addConstraint $ WellFormedMatchCond env matchUnknown
        condUnknown <- Unknown Map.empty <$> freshId "C"
        forM_ envs $ \env -> addConstraint $ WellFormedCond env condUnknown
        cut $ do
            p0 <- generateEOrError (zip (map (addAssumption matchUnknown . addAssumption condUnknown) envs) ts)
            matchValuation <- Set.toList <$> currentValuation matchUnknown
            let matchVars = Set.toList $ Set.unions (map varsOf matchValuation)
            condValuation <- currentValuation condUnknown
            let badError = isError p0 && length matchVars /= 1 -- null matchValuation && (not $ Set.null condValuation) -- Have we abduced a nontrivial vacuousness condition that is not a match branch?
            writeLog 3 $ text "Match valuation" <+> pretty matchValuation <+> if badError then text ": discarding error" else empty
            guard $ not badError -- Such vacuousness conditions are not productive (do not add to the environment assumptions and can be discovered over and over infinitely)
            let matchConds = map (conjunction . Set.fromList . (\var -> filter (Set.member var . varsOf) matchValuation)) matchVars -- group by vars
            d <- asks . view $ _1 . matchDepth -- Backtrack if too many matches, maybe we can find a solution with fewer
            guard $ length matchConds <= d
            return (matchConds, conjunction condValuation, p0)

    generateEOrError ws = generateError (map fst ws) `mplus` generateE ws

    generateOtherBranches :: MonadHorn s => ([Formula], Formula, RWProgram) -> Explorer s RWProgram
    generateOtherBranches (matchConds, conds, p0) = do
        pThen <- cut $ generateMatchesFor (map (addAssumption conds) envs) matchConds p0 ts
        -- TODO:(mj) This feels weird to use repeat conds here. But I'm not sure what it should be.
        generateElse ws (replicate (length ws) conds) pThen

    generateMatchesFor :: MonadHorn s => [Environment] -> [Formula] -> RWProgram -> TypeVector -> Explorer s RWProgram
    generateMatchesFor envs [] pBaseCase t = return pBaseCase
    generateMatchesFor envs (matchCond : rest) pBaseCase t = do
        let (Binary Eq matchVar@(Var _ x) (Cons _ c _)) = matchCond
        scrTs <- forM envs (\env -> runInSolver $ currentAssignment (toMonotype $ symbolsOfArity 0 env Map.! x))
        let (ScalarT (DatatypeT scrDT _ _) _) = head scrTs
        let pScrutinee = Program (PSymbol x) scrTs
        let ctors = ((head envs ^. datatypes) Map.! scrDT) ^. constructors
        let envs' = map (addScrutinee pScrutinee) envs
        pBaseCase' <-
            cut $
                inContext (\p -> Program (PMatch pScrutinee [Case c [] p]) ts) $
                    generateMatchesFor (map (addAssumption matchCond) envs') rest pBaseCase ts

        let genOtherCases previousCases ctors =
                case ctors of
                    [] -> return $ Program (PMatch pScrutinee previousCases) ts
                    (ctor : rest) -> do
                        (c, recheck) <- cut $ generateCase envs' (replicate (length ws) matchVar) pScrutinee ts ctor
                        ifM
                            (tryEliminateBranching (expr c) recheck)
                            (return $ expr c)
                            (genOtherCases (previousCases ++ [c]) rest)

        genOtherCases [Case c [] pBaseCase] (delete c ctors)

-- | 'generateE' @env typ@ : explore all elimination terms of type @typ@ in environment @env@
-- (bottom-up phase of bidirectional typechecking)
generateE :: MonadHorn s => [World] -> Explorer s RWProgram
generateE ws = do
  putMemo Map.empty                                     -- Starting E-term enumeration in a new environment: clear memoization store
  d <- asks . view $ _1 . eGuessDepth
  (Program pTerm pTyps) <- generateEUpTo ws d                            -- Generate the E-term
  logItFrom "generateE" $ text "got program to check:" <+> pretty (Program pTerm pTyps)
  runInSolver $ isFinal .= True >> solveTypeConstraints >> isFinal .= False  -- Final type checking pass that eliminates all free type variables
  logItFrom "generateE" $ text "all FV gone in type"
  newGoals <- uses auxGoals (map gName)                                      -- Remember unsolved auxiliary goals
  generateAuxGoals                                                           -- Solve auxiliary goals
  logItFrom "generateE" $ text "solved all aux goals"
  pTyps' <- mapM (runInSolver . currentAssignment) pTyps                     -- Finalize the type of the synthesized term
  logItFrom "generateE" $ text "finalized type:" <+> pretty pTyps'
  addLambdaLets pTyps' (Program pTerm pTyps') newGoals                        -- Check if some of the auxiliary goal solutions are large and have to be lifted into lambda-lets
  where
    addLambdaLets :: MonadHorn s => TypeVector -> RWProgram -> [Id] -> Explorer s RWProgram
    addLambdaLets ts body [] = return body
    addLambdaLets ts body (g:gs) = do
      pAux <- uses solvedAuxGoals (Map.! g)
      if programNodeCount pAux > 5
        then addLambdaLets ts (Program (PLet g uHoleWorld body) ts) gs
        else addLambdaLets ts body gs

-- | 'generateEUpTo' @env typ d@ : explore all applications of type shape @shape typ@ in environment @env@ of depth up to @d@
generateEUpTo :: MonadHorn s => [World] -> Int -> Explorer s RWProgram
generateEUpTo ws d =
  mplus (msum $ map (generateEAt ws) [0..d]) $
        (throwErrorWithDescription (text "no more programs."))

-- | 'generateEAt' @env typ d@ : explore all applications of type shape @shape typ@ in environment @env@ of depth exactly to @d@
generateEAt :: MonadHorn s => [World] -> Int -> Explorer s RWProgram
generateEAt _ d | d < 0 = mzero
generateEAt ws d = do
  useMem <- asks . view $ _1 . useMemoization
  if not useMem || d == 0
    then do -- Do not use memoization
      logItFrom "generateEAt" $ text ("d = " ++ show d)
      p <- enumerateAt ws d
      checkE ws p
      return p
    else do -- Try to fetch from memoization store
      $(todo "generateEAt with Memoization")
      -- startState <- get
      -- let tass = startState ^. typingState . typeAssignment
      -- let memoKey = MemoKey (arity typ) (shape $ typeSubstitute tass (lastType typ)) startState d
      -- startMemo <- getMemo
      -- case Map.lookup memoKey startMemo of
      --   Just results -> do -- Found memoized results: fetch
      --     logItFrom "generateEAt" (text "Fetching for:" <+> pretty memoKey $+$
      --                 text "Result:" $+$ vsep (map (\(p, _) -> pretty p) results))
      --     msum $ map applyMemoized results
      --   Nothing -> do -- Nothing found: enumerate and memoize
      --     logItFrom "generateEAt" (text "Nothing found for:" <+> pretty memoKey)
      --     p <- enumerateAt ws d

      --     memo <- getMemo
      --     finalState <- get
      --     let memo' = Map.insertWith (flip (++)) memoKey [(p, finalState)] memo
      --     logItFrom "generateEAt" (text "Memoizing for:" <+> pretty memoKey <+> pretty p <+> text "::" <+> pretty (typeOf p))

      --     putMemo memo'

      --     checkE ws p
      --     return p
  where
    applyMemoized (p, finalState) = do
      put finalState
      checkE ws p
      return p

-- | Perform a gradual check that @p@ has type @typ@ in @env@:
-- if @p@ is a scalar, perform a full subtyping check;
-- if @p@ is a (partially applied) function, check as much as possible with unknown arguments
checkE :: MonadHorn s => [World] -> RWProgram -> Explorer s [Int]
checkE ws p@(Program pTerm pTyps) = do
  let typs = map snd ws
  ctx <- asks . view $ _1 . context
  doesCheckForAll <- asks . view $ _1 . intersectAllMustCheck
  writeLog 2 empty 
  writeLog 2 $ brackets (text "checkE") <+> text "Checking" <+> pretty p <+> text "::" <+> pretty typs <+> text "in" $+$ pretty (ctx $ untypedWorld PHole)
  let ws' = addListToZip ws pTyps

  -- ifM (asks $ _symmetryReduction . fst) checkSymmetry (return ())

  incremental <- asks . view $ _1 . incrementalChecking -- Is incremental type checking of E-terms enabled?
  consistency <- asks . view $ _1 . consistencyChecking -- Is consistency checking enabled?

  let idxdws = zip ws' ([1..]::[Int])
  let combinator = if doesCheckForAll
      then forM idxdws
      else (\f -> observeAllT $ lift $ msum $ map f idxdws)

  let checker = \((env, typ, pTyp), idx) -> do
                    logItFrom "checkE" $ pretty (void p) <+> text "chk" <+> pretty typ <+> text "str" <+> pretty pTyp
                    when (incremental || arity typ == 0) (addConstraint $ Subtype env pTyp typ False "checkE-subtype") -- Add subtyping check, unless it's a function type and incremental checking is diasbled
                    when (consistency && arity typ > 0) (addConstraint $ Subtype env pTyp typ True "checkE-consistency") -- Add consistency constraint for function types
                    fTyp <- runInSolver $ finalizeType typ
                    logItFrom "checkE" (text "finalized type:" <+> pretty fTyp)
                    pos <- asks . view $ _1 . sourcePos
                    typingState . errorContext .= (pos, text "when checking" </> pretty p <+> text "::" <+> pretty fTyp </> text "in" $+$ pretty (ctx p))
                    runInSolver solveTypeConstraints
                    typingState . errorContext .= (noPos, empty)
                    writeLog 2 $ text "Checking OK:" <+> pretty p <+> text "::" <+> pretty fTyp <+> text "in" $+$ pretty (ctx (untypedWorld PHole))
                    return idx

  -- let t1 = map checker ws'
  -- sequence_ t1
  worlds <- combinator checker
  logItFrom "checkE" $ text "combinator complete:" <+> pretty worlds
  return worlds

checkSymbol :: MonadHorn s => [World] -> Id -> Explorer s RWProgram
checkSymbol ws name = do
  intersectionStrat <- asks . view $ _1 . intersectStrategy
  ts <- forM ws $ \(env, typ) ->
    case lookupSymbol name (arity typ) (hasSet typ) env of
      Nothing -> throwErrorWithDescription $ text "Not in scope:" </> text name
      Just sch -> do
        logItFrom "checkSymbol" $ dquotes (text name) <+> text "schema:" <+> pretty sch <+> text "against" <+> pretty typ
        t' <- symbolType env name sch  -- symbolType will infer a type if it's polymorphic or an intersection
        -- logItFrom "reconstructE'-Var-Base" (text "symbol:" <+> (pretty name) <> (text "::") <> (pretty typ) <+> (text "symbol type:")  <+> (pretty t'))
        case intersectionStrat of

          {- Select one side of an intersection -}
          EitherOr -> do -- $(todo "eitherOr") {-
          -- do
            let ts = intersectionToList t'
            let nameShape = head . intersectionToList <$> Map.lookup name (env ^. shapeConstraints)

          --   -- t could be an intersection, loop over choices
            symbolUseCount %= Map.insertWith (+) name 1
            let iterList = zip ts [1..]
            let choices = flip map iterList $ \(t, idx) -> do
                  logItFrom "reconstructE" $ brackets (text "PSymbol") 
                    <> text ": making choice"
                    <+> parens ((text $ show idx) <> text "/" <> (text $ show $ length iterList))
                    <+> text "for" <+> text name
                    <> L.nest 4 (L.line <> (text "type:" <+> pretty t) L.<$> (text "shape:" <+> pretty nameShape))

                  let p = Program (PSymbol name) t
                  -- if the shape was an intersection, all parts of the intersection should all have the same shape.
                  case nameShape of
                    Nothing -> return ()
                    Just sc -> addConstraint $ Subtype env (refineBot env $ shape t) (refineTop env sc) False "var-eitherOr-shape-match"
                  -- _ <- checkE [(env, typ)] (convertToNWorlds p 1)
                  -- return $ convertToNWorlds p 1
                  return t
            msum choices

          {- Base rule -}
          _ -> return t'
  symbolUseCount %= Map.insertWith (+) name 1
  let p = Program (PSymbol name) ts
  checkE ws p
  return p


enumerateAt :: MonadHorn s => [World] -> Int -> Explorer s RWProgram
enumerateAt ws 0 = do
    -- All symbols, for each world, of the correct arity in that world.
    let initSymbols = concatMap (\(env, typ) -> Map.toList $ symbolsOfArity (arity typ) env) ws
                    & nubOrd
    -- Only those symbols that could fit by the shape.
    symbols'' <- nubOrd . map fst <$> (`foldM` initSymbols) (\symbols (env, typ)-> do
      useCounts <- use symbolUseCount
      let symbols' = filter (\(x, _) -> x `notElem` setConstructors) $ if arity typ == 0
                          then sortBy (mappedCompare (\(x, _) -> (Set.member x (env ^. constants), Map.findWithDefault 0 x useCounts))) symbols
                          else sortBy (mappedCompare (\(x, _) -> (not $ Set.member x (env ^. constants), Map.findWithDefault 0 x useCounts))) symbols
      return symbols') ws
    logItFrom "enumerateAt" $ text "Symbols:" <+> pretty symbols''
    msum $ map (checkSymbol ws) symbols''

enumerateAt ws d = do
  forM_ ws $ \(env, typ) -> do
    let maxArity = fst $ Map.findMax (env ^. symbols)
    guard $ arity typ < maxArity
  generateAllApps
  where
    appParams = (True, local (over (_1 . eGuessDepth) (-1 +)))
    generateAllApps =
      generateApp appParams ws (\ws -> generateEUpTo ws (d - 1)) (\ws -> generateEAt ws (d - 1)) `mplus`
        generateApp appParams ws (\ws -> generateEAt ws d) (\ws -> generateEUpTo ws (d - 1))
        -- `mplus` $(todo "Should we also support (APP (d-1) (d))?")

generateApp :: MonadHorn s =>
  -- Some parameters to allow us to use this in synth and checking.
  (Bool, Explorer s RWProgram -> Explorer s RWProgram) ->
  [World] ->
  ([World] -> Explorer s RWProgram) ->
  ([World] -> Explorer s RWProgram) ->
    Explorer s RWProgram
generateApp (enableCut, ctxMod) ws genFun genArg = do
  x <- freshId "X"
  let retTyps = map snd ws
  let functionWorlds = map (second (FunctionT x AnyT)) ws
  pFun <- inContext (\p -> Program (PApp p uHoleWorld) retTyps)
            $ genFun functionWorlds -- Find all functions that unify with (? -> typ)
  -- let FunctionT x tArg tRes = typeOf fun
  let funTypes = typeOf pFun
  let argTypes' = map argType funTypes
  let realArgs = map (\(FunctionT y _ _) -> y) funTypes
  let retTypes' = map resType funTypes

  if argTypes' & head & isFunctionType
    then do -- Higher-order argument: its value is not required for the function type, return a placeholder and enqueue an auxiliary goal
      $(todo "HOF goals, should they be world goals? I think yes.")
      -- d <- asks . view $ _1 . auxDepth
      -- when (d <= 0) $ writeLog 2 (text "Cannot synthesize higher-order argument: no auxiliary functions allowed") >> mzero
      -- arg <- enqueueGoal env tArg (untyped PHole) (d - 1)
      -- return $ Program (PApp fun arg) tRes
    else do -- First-order argument: generate now
      let mbCut = id -- if (not enableCut) && Set.member x (varsOfType tRes) then id else cut
      let argWorlds = zip (map fst ws) argTypes'
      arg <- ctxMod
                $ inContext (\p -> Program (PApp pFun p) retTypes')
                $ mbCut (genArg argWorlds)
      writeLog 3 (text "Synthesized argument" <+> pretty arg <+> text "of type" <+> pretty (typeOf arg))

      let appWorlds = zip (map fst ws) retTypes'
      let tRes' = appTypes appWorlds arg realArgs
      return $ Program (PApp pFun arg) tRes'

-- | Make environments inconsistent (if possible with current unknown assumptions)
generateError :: MonadHorn s => [Environment] -> Explorer s RWProgram
generateError envs = do
  ctx <- asks . view $ _1. context
  writeLog 2 $ text "Checking Error Program" <+> pretty errorProgram <+> text "in" $+$ pretty (ctx errorProgram)
  tass <- use (typingState . typeAssignment)
  let envs' = map (typeSubstituteEnv tass) envs
  zipWithM_ (\env env' ->
      addConstraint $ Subtype env
          (int $ conjunction $ Set.fromList $ map trivial (allScalars env'))
          (int ffalse) False "")
      envs envs'
  pos <- asks . view $ _1 . sourcePos
  typingState . errorContext .= (pos, text "when checking" </> pretty errorProgram </> text "in" $+$ pretty (ctx errorProgram))
  runInSolver solveTypeConstraints
  typingState . errorContext .= (noPos, empty)
  return errorProgram
  where
    trivial var = var |=| var

-- | 'toVar' @p env@: a variable representing @p@ (can be @p@ itself or a fresh ghost)
toVar :: MonadHorn s => [Environment] -> RWProgram -> Explorer s ([Environment], [Formula])
toVar envs (Program (PSymbol name) ts) = return (envs, zipWith (\env t -> symbolAsFormula env name t) envs ts)
toVar envs (Program _ ts) = unzip <$> zipWithM (\env t -> do
  g <- freshId "G"
  return (addLetBound g t env, (Var (toSort $ baseTypeOf t) g))) envs ts

-- | 'appType' @env p x tRes@: a type semantically equivalent to [p/x]tRes;
-- if @p@ is not a variable, instead of a literal substitution use the contextual type LET x : (typeOf p) IN tRes
appType :: Environment -> RProgram -> Id -> RType -> RType
appType env (Program (PSymbol name) t) x tRes = substituteInType (isBound env) (Map.singleton x $ symbolAsFormula env name t) tRes
appType env (Program _ t) x tRes = contextual x t tRes

-- | 'appTypes' @ws p xs@: The ws contains (env, tRes)_i. This creates
-- a type semantically equivalent to:
-- forall i in worlds; [p/x_i](w_i tRes) if the original function had type (x_i:_ -> _) in w_i
-- if @p@ is not a variable, instead of a literal substitution, use the
-- contextual type (LET x : i-th typeOf p) in i-th tRes)_i
appTypes :: [World] -> RWProgram -> [Id] -> TypeVector
appTypes ws (Program (PSymbol name) ts) xs =
  let (envs, tRess) = unzip ws
   in zipWith4 (\env tRes t x -> appType env (Program (PSymbol name) t) x tRes) envs tRess ts xs
appTypes ws (Program _ ts) xs =
  let (envs, tRess) = unzip ws
   in zipWith4 (\_ tRes t x -> contextual x t tRes) envs tRess ts xs


isPolyConstructor (Program (PSymbol name) t) = isTypeName name && (not . Set.null . typeVarsOf $ t)

enqueueGoal env typ impl depth = do
  g <- freshVar env "f"
  auxGoals %= ((Goal g env (Monotype typ) impl depth noPos True) :)
  return $ Program (PSymbol g) typ

{- Utility -}

-- | Get memoization store
getMemo :: MonadHorn s => Explorer s Memo
getMemo = lift . lift . lift $ use termMemo

-- | Set memoization store
putMemo :: MonadHorn s => Memo -> Explorer s ()
putMemo memo = lift . lift . lift $ termMemo .= memo

-- getPartials :: MonadHorn s => Explorer s PartialMemo
-- getPartials = lift . lift . lift $ use partialFailures

-- putPartials :: MonadHorn s => PartialMemo -> Explorer s ()
-- putPartials partials = lift . lift . lift $ partialFailures .= partials

throwErrorWithDescription :: MonadHorn s => Doc -> Explorer s a
throwErrorWithDescription msg = do
  pos <- asks . view $ _1 . sourcePos
  throwError $ ErrorMessage TypeError pos msg

-- | Record type error and backtrack
throwError :: MonadHorn s => ErrorMessage -> Explorer s a
throwError e = do
  currentGoal <- use $ typingState . topLevelGoal
  writeLog 2 $ text "TYPE ERROR:" </> text "from world:" <+> pretty currentGoal </> text "with error:" <+> plain (emDescription e)
  lift . lift . lift $ typeErrors %= (e :)
  mzero

-- | Impose typing constraint @c@ on the programs
addConstraint c = typingState %= addTypingConstraint c

-- | Embed a type-constraint checker computation @f@ in the explorer; on type error, record the error and backtrack
runInSolver :: MonadHorn s => TCSolver s a -> Explorer s a
runInSolver f = do
  tParams <- asks . view $ _2
  tState <- use typingState
  res <- lift . lift . lift . lift $ runTCSolver tParams tState f
  case res of
    Left err -> do
      logItFrom "runInSolver" $ text "Type Checker returned error:"
      throwError err
    Right (res, st) -> do
      typingState .= st
      return res

freshId :: MonadHorn s => String -> Explorer s String
freshId = runInSolver . TCSolver.freshId

freshVar :: MonadHorn s => Environment -> String -> Explorer s String
freshVar env prefix = runInSolver $ TCSolver.freshVar env prefix

fresh :: MonadHorn s => Environment -> RType -> Explorer s RType
fresh env t = runInSolver $ TCSolver.fresh env t

freshFromIntersect :: MonadHorn s => Environment -> RType -> Explorer s RType
freshFromIntersect env t = do
  currentGoal <- use $ typingState . topLevelGoal
  runInSolver $ TCSolver.freshFromIntersect env t currentGoal

-- | Return the current valuation of @u@;
-- in case there are multiple solutions,
-- order them from weakest to strongest in terms of valuation of @u@ and split the computation
currentValuation :: MonadHorn s => Formula -> Explorer s Valuation
currentValuation u = do
  runInSolver $ solveAllCandidates
  cands <- use (typingState . candidates)
  let candGroups = groupBy (\c1 c2 -> val c1 == val c2) $ sortBy (\c1 c2 -> setCompare (val c1) (val c2)) cands
  msum $ map pickCandidiate candGroups
  where
    val c = valuation (solution c) u
    pickCandidiate cands' = do
      typingState . candidates .= cands'
      return $ val (head cands')

-- inContext ctx f = local (over (_1 . context) (. ctx)) f
inContext ctx f = withSetting context (. ctx) f

atLeastOneWorld f = withSetting intersectAllMustCheck (const False) f

withSetting setting value f = local (over (_1 . setting) value) f

-- | Replace all bound type and predicate variables with fresh free variables
-- (if @top@ is @False@, instantiate with bottom refinements instead of top refinements)
instantiate :: MonadHorn s => Environment -> RSchema -> Bool -> [Id] -> Explorer s RType
instantiate env sch top argNames = do
  t <- instantiate' Map.empty Map.empty sch
  writeLog 3 (text "INSTANTIATE" <+> pretty sch $+$ text "INTO" <+> pretty t)
  return t
  where
    instantiate' subst pSubst (ForallT a sch) = do
      a' <- freshId "A"
      addConstraint $ WellFormed env (vart a' ftrue)
      instantiate' (Map.insert a (vart a' (BoolLit top)) subst) pSubst sch
    instantiate' subst pSubst (ForallP (PredSig p argSorts _) sch) = do
      let argSorts' = map (sortSubstitute (asSortSubst subst)) argSorts
      fml <- if top
              then do
                p' <- freshId (map toUpper p)
                addConstraint $ WellFormedPredicate env argSorts' p'
                return $ Pred BoolS p' (zipWith Var argSorts' deBrujns)
              else return ffalse
      instantiate' subst (Map.insert p fml pSubst) sch
    instantiate' subst pSubst (Monotype t) = do
      intersectionStrat <- asks . view $ _1 . intersectStrategy
      go subst pSubst intersectionStrat argNames t

    constrainBottom subst pSubst intersectionStrat argNames t = do
      medianType <- freshFromIntersect env t
      unless (isFunctionType medianType) $
        error "varInferMedian: Goal type not a function!"
      addConstraint $ WellFormed env medianType
      addConstraint $ Subtype env t medianType False "instantiate-isect-LHS"
      -- The G |- medianType <: goalType happens back in the PSymbol rule
      -- medianType <- varInferMedian env t
      go subst pSubst intersectionStrat argNames medianType

    go subst pSubst intersectionStrat argNames t@(FunctionT x tArg tRes) = do
      x' <- case argNames of
              [] -> freshVar env "X"
              (argName : _) -> return argName
      liftM2 (FunctionT x') (go subst pSubst intersectionStrat [] tArg) (go subst pSubst intersectionStrat (drop 1 argNames) (renameVar (isBoundTV subst) x x' tArg tRes))

    go subst pSubst intersectionStrat@InferMedian argNames t@AndT{} =
      constrainBottom subst pSubst intersectionStrat argNames t

    go subst pSubst intersectionStrat@AlgorithmicLaurent argNames t@AndT{} = do
      constrainBottom subst pSubst intersectionStrat argNames t

    go subst pSubst intersectionStrat@GuardedPowerset argNames t@AndT{} = do
      constrainBottom subst pSubst intersectionStrat argNames t

    -- Use a Laurent-presentation of BCD to infer a median type from some
    -- subset of the intersected types.
    go subst pSubst intersectionStrat@LaurentBCD argNames t@AndT{} = do
      let conjuncts = intersectionToList t
      let tpowerset = map Set.toList . Set.toList . Set.delete Set.empty . Set.powerSet . Set.fromList $ conjuncts
      let choices = flip map (zip tpowerset [1..]) $ \(ts, idx) -> do
            let total = length tpowerset
            let t = listToIntersection ts
            writeLog 3 $ text "choice" <+> parens (text (show idx) <> text "/" <> text (show total)) <> text ":" <+> pretty t
            medianType <- fresh env t
            unless (isFunctionType medianType) $
              error "varInferMedian: Goal type not a function!"
            addConstraint $ WellFormed env medianType
            addConstraint $ Subtype env t medianType False "instantiate-isect-LHS"
            return medianType
      choice <- msum choices
      -- Now try to infer the medium type
      go subst pSubst intersectionStrat argNames choice

    go subst pSubst _ _ t = return $ typeSubstitutePred pSubst . typeSubstitute subst $ t


    isBoundTV subst a = (a `Map.member` subst) || (a `elem` (env ^. boundTypeVars))

-- | 'symbolType' @env x sch@: precise type of symbol @x@, which has a schema @sch@ in environment @env@;
-- if @x@ is a scalar variable, use "_v == x" as refinement;
-- if @sch@ is a polytype, return a fresh instance
symbolType :: MonadHorn s => Environment -> Id -> RSchema -> Explorer s RType
symbolType env x (Monotype t@(ScalarT b _))
    | isLiteral x = return t -- x is a literal of a primitive type, it's type is precise
    | isJust (lookupConstructor x env) = return t -- x is a constructor, it's type is precise
    | otherwise = return $ ScalarT b (varRefinement x (toSort b)) -- x is a scalar variable or monomorphic scalar constant, use _v = x
symbolType env _ sch = freshInstance sch
  where
    freshInstance sch = if arity (toMonotype sch) == 0
      then instantiate env sch False [] -- Nullary polymorphic function: it is safe to instantiate it with bottom refinements, since nothing can force the refinements to be weaker
      else instantiate env sch True []

-- | Perform an exploration, and once it succeeds, do not backtrack it
cut :: MonadHorn s => Explorer s a -> Explorer s a
cut = once

-- | Synthesize auxiliary goals accumulated in @auxGoals@ and store the result in @solvedAuxGoals@
generateAuxGoals :: MonadHorn s => Explorer s ()
generateAuxGoals = do
  goals <- use auxGoals
  writeLog 3 $ text "Auxiliary goals are:" $+$ vsep (map pretty goals)
  case goals of
    [] -> return ()
    (g : gs) -> do
        auxGoals .= gs
        writeLog 2 $ text "PICK AUXILIARY GOAL" <+> pretty g
        Reconstructor reconstructTopLevel <- asks . view $ _3
        p <- reconstructTopLevel g
        solvedAuxGoals %= Map.insert (gName g) (etaContract p)
        generateAuxGoals
  where
    etaContract p = case etaContract' [] (content p) of
                      Nothing -> p
                      Just f -> Program f (typeOf p)
    etaContract' [] (PFix _ p)                                               = etaContract' [] (content p)
    etaContract' binders (PFun x p)                                          = etaContract' (x:binders) (content p)
    etaContract' (x:binders) (PApp pFun (Program (PSymbol y) _)) | x == y    =  etaContract' binders (content pFun)
    etaContract' [] f@(PSymbol _)                                            = Just f
    etaContract' binders p                                                   = Nothing

writeLog level msg = do
  maxLevel <- asks . view $ _1 . explorerLogLevel
  if level <= maxLevel then traceShow (plain msg) $ return () else return ()

logItFrom fnName msg = do
  writeLog 1 $ brackets (text fnName) <+> msg
