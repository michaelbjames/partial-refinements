{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, FlexibleInstances #-}

-- | Solver for second-order constraints
module Synquid.HornSolver (
    CandidatePickStrategy (..)
  , ConstraintPickStrategy (..)
  , OptimalValuationsStrategy (..)
  , HornSolverParams (..)
  , FixPointSolver
  , evalFixPointSolver
  ) where

import Synquid.Logic
import Synquid.SolverMonad
import Synquid.Util
import Synquid.Pretty

import Data.List
import Data.Maybe
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Foldable as F

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import Control.Applicative
import Control.Lens hiding (both)

import Debug.Trace

{- Interface -}

-- | Strategies for picking the next candidate solution to strengthen
data CandidatePickStrategy = FirstCandidate | WeakCandidate | InitializedWeakCandidate
      
-- | Strategies for picking the next constraint to solve      
data ConstraintPickStrategy = FirstConstraint | SmallSpaceConstraint

-- | MUS search strategies
data OptimalValuationsStrategy = BFSValuations | MarcoValuations

-- | Parameters of the fix point algorithm
data HornSolverParams = HornSolverParams {
  pruneQuals :: Bool,                                     -- ^ Should redundant qualifiers be removed before solving constraints?
  optimalValuationsStrategy :: OptimalValuationsStrategy, -- ^ How should we find optimal left-hand side valuations?
  semanticPrune :: Bool,                                  -- ^ After solving each constraints, remove semantically non-optimal solutions
  agressivePrune :: Bool,                                 -- ^ Perform pruning on the LHS-pValuation of as opposed to per-variable valuations
  candidatePickStrategy :: CandidatePickStrategy,         -- ^ How should the next candidate solution to strengthen be picked?
  constraintPickStrategy :: ConstraintPickStrategy,       -- ^ How should the next constraint to solve be picked?
  solverLogLevel :: Int                                   -- ^ How verbose logging is
}

-- | Fix point solver execution 
type FixPointSolver s = ReaderT HornSolverParams s

evalFixPointSolver = runReaderT

instance MonadSMT s => MonadHorn (FixPointSolver s) where
  initHornSolver = do
    lift initSolver
    return $ Candidate (topSolution Map.empty) Set.empty Set.empty "0"
    
  refine = refineCandidates
  
  pruneQualifiers quals = ifM (asks pruneQuals) (pruneQSpace quals) (return quals)
  
  checkConsistency = check
 
{- Implementation -}

-- | 'refineCandidates' @params quals constraints cands@ : solve @constraints@ using @quals@ starting from initial candidates @cands@;
-- if there is no solution, produce an empty list of candidates; otherwise the first candidate in the list is a complete solution
refineCandidates :: MonadSMT s => [Formula] -> QMap -> ExtractAssumptions -> [Candidate] -> FixPointSolver s [Candidate]
refineCandidates constraints quals extractAssumptions cands = do
    writeLog 1 (vsep [nest 2 $ text "Constraints" $+$ vsep (map pretty constraints), nest 2 $ text "QMap" $+$ pretty quals])
    let constraints' = filter isNew constraints
    cands' <- mapM (addConstraints constraints') cands
    case find (Set.null . invalidConstraints) cands' of
      Just c -> return $ c : delete c cands'
      Nothing -> greatestFixPoint quals extractAssumptions cands'      
  where      
    isNew c = not (c `Set.member` validConstraints (head cands)) && not (c `Set.member` invalidConstraints (head cands))
      
    addConstraints constraints (Candidate sol valids invalids label) = do
      let sol' = merge (topSolution quals) sol  -- Add new unknowns
      (valids', invalids') <- partitionM (isValidFml . hornApplySolution extractAssumptions sol') constraints -- Evaluate new constraints
      return $ Candidate sol' (valids `Set.union` Set.fromList valids') (invalids `Set.union` Set.fromList invalids') label

-- | 'check' @fmls cands@ : return those candidates from @cands@ under which all @fmls@ are satisfiable
check :: MonadSMT s => [Formula] -> [Candidate] -> FixPointSolver s [Candidate]
check fmls cands = do
    writeLog 1 (vsep [nest 2 $ text "Consistency" $+$ vsep (map pretty fmls), nest 2 $ text "Candidates" <+> parens (pretty $ length cands) $+$ (vsep $ map pretty cands)])
    cands' <- filterM checkCand cands
    writeLog 1 (nest 2 $ text "Remaining Candidates" <+> parens (pretty $ length cands') $+$ (vsep $ map pretty cands'))
    return cands'
  where
    checkCand (Candidate sol valids invalids label) = let fmls' = map (applySolution sol) fmls 
      in not <$> anyM isValidFml (map fnot fmls')

-- | 'greatestFixPoint' @quals constraints@: weakest solution for a system of second-order constraints @constraints@ over qualifiers @quals@.
greatestFixPoint :: MonadSMT s => QMap -> ExtractAssumptions -> [Candidate] -> FixPointSolver s [Candidate]
greatestFixPoint _ _ [] = return []
greatestFixPoint quals extractAssumptions candidates = do
    (cand@(Candidate sol _ _ _), rest) <- pickCandidate candidates <$> asks candidatePickStrategy
    fml <- asks constraintPickStrategy >>= pickConstraint cand
    let modifiedConstraint = instantiateRhs sol fml 
    debugOutput candidates cand fml modifiedConstraint
    diffs <- strengthen quals modifiedConstraint sol                        
    (newCandidates, rest') <- if length diffs == 1
      then do -- Propagate the diff to all equivalent candidates
        let unknowns = Set.map unknownName $ unknownsOf fml
        let (equivs, nequivs) = partition (\(Candidate s valids invalids _) -> restrictDomain unknowns s == restrictDomain unknowns sol && Set.member fml invalids) rest
        nc <- mapM (\c -> updateCandidate fml c diffs (head diffs)) (cand : equivs)
        return (nc, nequivs)
      else do -- Only update the current candidate
        nc <- mapM (updateCandidate fml cand diffs) diffs
        return (nc, rest)
    case find (Set.null . invalidConstraints) newCandidates of
      Just cand' -> return $ cand' : (delete cand' newCandidates ++ rest')  -- Solution found
      Nothing -> greatestFixPoint quals extractAssumptions (newCandidates ++ rest')

  where
    instantiateRhs sol fml = case fml of
      Binary Implies lhs rhs -> let
         rhs' = applySolution sol rhs
         assumptions = extractAssumptions rhs'
        in Binary Implies (lhs `andClean` conjunction assumptions) rhs'
      _ -> error $ unwords ["greatestFixPoint: encountered ill-formed constraint", show fml]              
              
    -- | Re-evaluate affected clauses in @valids@ and @otherInvalids@ after solution has been strengthened from @sol@ to @sol'@ in order to fix @fml@
    updateCandidate fml (Candidate sol valids invalids label) diffs diff = do
      let sol' = merge sol diff
      let modifiedUnknowns = Map.keysSet $ Map.filter (not . Set.null) diff
      let (unaffectedValids, affectedValids) = Set.partition (\fml -> posUnknowns fml `disjoint` modifiedUnknowns) valids
      let (unaffectedInvalids, affectedInvalids) = Set.partition (\fml -> negUnknowns fml `disjoint` modifiedUnknowns) (Set.delete fml invalids)
      (newValids, newInvalids) <- setPartitionM (isValidFml . hornApplySolution extractAssumptions sol') $ affectedValids `Set.union` affectedInvalids
      let newLabel = if length diffs == 1 then label else label ++ "." ++ show (fromJust $ elemIndex diff diffs)
      return $ Candidate sol' (Set.insert fml $ unaffectedValids `Set.union` newValids) (unaffectedInvalids `Set.union` newInvalids) newLabel
      
    nontrivCount = Map.size . Map.filter (not . Set.null) -- number of unknowns with a non-top valuation
    totalQCount = sum . map Set.size . Map.elems          -- total number of qualifiers in a solution
          
    pickCandidate :: [Candidate] -> CandidatePickStrategy -> (Candidate, [Candidate])
    pickCandidate (cand:rest) FirstCandidate = (cand, rest)
    pickCandidate cands WeakCandidate = let 
        res = maximumBy (mappedCompare $ \(Candidate s valids invalids _) -> (- totalQCount s)) cands  -- minimize strength
      in (res, delete res cands)
    pickCandidate cands InitializedWeakCandidate = let 
        res = maximumBy (mappedCompare $ \(Candidate s valids invalids _) -> (nontrivCount s, - totalQCount s, Set.size valids + Set.size invalids)) cands  -- maximize the number of initialized unknowns and minimize strength
      in (res, delete res cands)
      
    pickConstraint (Candidate sol valids invalids _) strategy = case strategy of
      FirstConstraint -> return $ Set.findMin invalids
      SmallSpaceConstraint -> do
        let spaceSize fml = maxValSize quals sol (unknownsOf (leftHandSide fml))
        return $ minimumBy (\x y -> compare (spaceSize x) (spaceSize y)) (Set.toList invalids)

    debugOutput cands cand inv modified =
      writeLog 1 (vsep [
        nest 2 $ text "Candidates" <+> parens (pretty $ length cands) $+$ (vsep $ map pretty cands), 
        text "Chosen candidate:" <+> pretty cand,
        text "Invalid Constraint:" <+> pretty inv,
        text "Strengthening:" <+> pretty modified])
        
hornApplySolution extractAssumptions sol fml = case fml of
  Binary Implies lhs rhs -> let
     rhs' = applySolution sol rhs
     assumptions = extractAssumptions rhs'
    in Binary Implies (applySolution sol lhs `andClean` conjunction assumptions) rhs'
  _ -> error $ unwords ["hornApplySolution: encountered ill-formed constraint", show fml]        
    
-- | 'strengthen' @quals fml sol@: all minimal strengthenings of @sol@ using qualifiers from @quals@ that make @fml@ valid;
-- | @fml@ must have the form "/\ u_i ==> const".
strengthen :: MonadSMT s => QMap -> Formula -> Solution -> FixPointSolver s [Solution]
strengthen quals fml@(Binary Implies lhs rhs) sol = do
    let n = maxValSize quals sol unknowns
    lhsValuations <- optimalValuations n (lhsQuals Set.\\ usedLhsQuals) usedLhsQuals rhs -- all minimal valid valuations of the whole antecedent
    writeLog 1 (text "Optimal valuations:" $+$ vsep (map pretty lhsValuations))
    let splitting = Map.filter (not . null) $ Map.fromList $ zip lhsValuations (map splitLhsValuation lhsValuations) -- map of lhsValuations with a non-empty split to their split
    let allSolutions = concat $ Map.elems splitting
    pruned <- ifM (asks semanticPrune) 
      (ifM (asks agressivePrune)
        (do 
          valuations' <- pruneValuations usedLhsQuals (Map.keys splitting) -- TODO: is this dangeorous??? the result might not cover the pruned alternatives in a different context!
          -- valuations' <- pruneValuations Set.empty (Map.keys splitting)
          writeLog 1 (text "Pruned valuations:" $+$ vsep (map pretty valuations'))
          return $ concatMap (splitting Map.!) valuations')   -- Prune LHS valuations and then return the splits of only optimal valuations
        (pruneSolutions unknownsList allSolutions))           -- Prune per-variable
      (return allSolutions)
    writeLog 1 (text "Diffs:" <+> parens (pretty $ length pruned) $+$ vsep (map pretty pruned))
    return pruned
  where
    unknowns = unknownsOf lhs
    knownConjuncts = conjunctsOf lhs Set.\\ unknowns
    unknownsList = Set.toList unknowns
    lhsQuals = setConcatMap (Set.fromList . lookupQualsSubst quals) unknowns   -- available qualifiers for the whole antecedent
    usedLhsQuals = setConcatMap (valuation sol) unknowns `Set.union` knownConjuncts      -- already used qualifiers for the whole antecedent
    rhsVars = Set.map varName $ varsOf rhs
        
      -- | All possible additional valuations of @u@ that are subsets of $lhsVal@.
    singleUnknownCandidates lhsVal u = let           
          qs = lookupQualsSubst quals u
          max = lookupQuals quals maxCount u
          used = valuation sol u
          n = Set.size used
      in Set.toList $ boundedSubsets (max - n) $ (Set.fromList qs Set.\\ used) `Set.intersection` lhsVal
    
      -- | All valid partitions of @lhsVal@ into solutions for multiple unknowns.
    splitLhsValuation :: Valuation -> [Solution]
    splitLhsValuation lhsVal = do
      unknownsVal <- mapM (singleUnknownCandidates lhsVal) unknownsList
      let isValidsplit ss s = Set.unions ss == s && sum (map Set.size ss) == Set.size s
      guard $ isValidsplit unknownsVal lhsVal
      return $ Map.fromListWith Set.union $ zipWith unsubst unknownsList unknownsVal
      
    unsubst u@(Unknown s name) quals = (name, Set.map (substitute (inverse s)) quals)
          
strengthen _ fml _ = error $ unwords ["strengthen: encountered ill-formed constraint", show fml]

-- | 'maxValSize' @quals sol unknowns@: Upper bound on the size of valuations of a conjunction of @unknowns@ when strengthening @sol@ 
maxValSize :: QMap -> Solution -> Set Formula -> Int 
maxValSize quals sol unknowns = let 
    usedQuals = setConcatMap (valuation sol) unknowns
  in Set.foldl (\n u -> n + lookupQuals quals maxCount u) 0 unknowns - Set.size usedQuals
  
optimalValuations :: MonadSMT s => Int -> Set Formula -> Set Formula -> Formula -> FixPointSolver s [Valuation]
optimalValuations maxSize quals lhs rhs = do
  strategy <- asks optimalValuationsStrategy
  case strategy of
    BFSValuations -> optimalValuationsBFS maxSize quals lhs rhs
    MarcoValuations -> optimalValuationsMarco quals lhs rhs    
    
-- | 'optimalValuations' @quals check@: all smallest subsets of @quals@ for which @check@ returns a solution.
optimalValuationsBFS :: MonadSMT s => Int -> Set Formula -> Set Formula -> Formula -> FixPointSolver s [Valuation]
optimalValuationsBFS maxSize quals lhs rhs = map qualsAt <$> filterSubsets (check . qualsAt) (length qualsList)
  where
    qualsList = Set.toList quals
    qualsAt = Set.map (qualsList !!)
    check val = let 
                  n = Set.size val 
                  lhs' = conjunction lhs `andClean` conjunction val                  
      in if 1 <= n && n <= maxSize
          then isValidFml $ lhs' |=>| rhs
          else return False
    
optimalValuationsMarco :: MonadSMT s => Set Formula -> Set Formula -> Formula -> FixPointSolver s [Valuation]
optimalValuationsMarco quals lhs rhs = map Set.fromList <$> lift (allUnsatCores fixedLhs fixedRhs qualsList)
  where
    qualsList = Set.toList quals
    fixedLhs = conjunction lhs
    fixedRhs = fnot rhs
                            
-- | 'filterSubsets' @check n@: all minimal subsets of indexes from [0..@n@) that satisfy @check@,
-- where @check@ is monotone (if a set satisfies @check@, then every superset also satisfies @check@);
-- performs breadth-first search.
filterSubsets :: MonadSMT s => (Set Int -> FixPointSolver s Bool) -> Int -> FixPointSolver s [Set Int]
filterSubsets check n = go [] [Set.empty]
  where
    go solutions candidates = if null candidates 
      then return solutions
      else let new = filter (\c -> not $ any (`Set.isSubsetOf` c) solutions) candidates
        in do
          results <- zip new <$> mapM check new
          let (valids, invalids) = partition snd results
          go (solutions ++ map fst valids) (concatMap children (map fst invalids))      
    children idxs = let lower = if Set.null idxs then 0 else Set.findMax idxs + 1
      in map (`Set.insert` idxs) [lower..(n - 1)]      
            
-- | 'pruneSolutions' @sols@: eliminate from @sols@ all solutions that are semantically stronger on all unknowns than another solution in @sols@ 
pruneSolutions :: MonadSMT s => [Formula] -> [Solution] -> FixPointSolver s [Solution]
pruneSolutions unknowns = let isSubsumed sol sols = anyM (\s -> allM 
                                (\u -> isValidFml $ (conjunction $ valuation sol u) |=>| (conjunction $ valuation s u)) unknowns) sols
  in prune isSubsumed
  
-- | 'pruneValuations' @vals@: eliminate from @vals@ all valuations that are semantically stronger than another pValuation in @vals@   
pruneValuations :: MonadSMT s => Set Formula -> [Valuation] -> FixPointSolver s [Valuation] 
pruneValuations assumptions = let isSubsumed val vals = let fml = conjunction (val `Set.union` assumptions) in anyM (\v -> isValidFml $ fml |=>| conjunction v) vals
  in prune isSubsumed
  
-- | 'pruneQualifiers' @quals@: eliminate logical duplicates from @quals@
pruneQSpace :: MonadSMT s => QSpace -> FixPointSolver s QSpace 
pruneQSpace qSpace = let isSubsumed qual quals = anyM (\q -> isValidFml $ qual |<=>| q) quals
  in do
    quals' <- filterM (\q -> ifM (isValidFml q) (return False) (not <$> isValidFml (fnot q))) (qSpace ^. qualifiers) 
    quals <- prune isSubsumed quals'
    return $ set qualifiers quals qSpace
  
-- | 'prune' @isSubsumed xs@ : prune all elements of @xs@ subsumed by another element according to @isSubsumed@  
prune :: MonadSMT s => (a -> [a] -> FixPointSolver s Bool) -> [a] -> FixPointSolver s [a]
prune _ [] = return []
prune isSubsumed (x:xs) = prune' [] x xs
  where
    prune' lefts x [] = ifM (isSubsumed x lefts) (return lefts) (return $ x:lefts)
    prune' lefts x rights@(y:ys) = ifM (isSubsumed x (lefts ++ rights)) (prune' lefts y ys) (prune' (lefts ++ [x]) y ys)  
              
-- | 'isValid' lifted to FixPointSolver      
isValidFml :: MonadSMT s => Formula -> FixPointSolver s Bool
isValidFml = lift . isValid

writeLog level msg = do
  maxLevel <- asks solverLogLevel
  if level <= maxLevel then traceShow msg $ return () else return ()
