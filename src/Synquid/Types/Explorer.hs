{-# LANGUAGE TemplateHaskell, FlexibleContexts, TupleSections, DeriveDataTypeable #-}
module Synquid.Types.Explorer where

import Synquid.Types.Logic
import Synquid.Types.Program
import Synquid.Types.Type
import Synquid.Types.Error
import Synquid.Types.Params
import Synquid.Types.Rest
import Synquid.Types.Solver
import Synquid.Util

import Control.Lens
import Data.Map
import Text.PrettyPrint.ANSI.Leijen
import Control.Monad.Logic
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except


-- | Parameters of program exploration
data ExplorerParams = ExplorerParams {
  _eGuessDepth :: Int,                    -- ^ Maximum depth of application trees
  _scrutineeDepth :: Int,                 -- ^ Maximum depth of application trees inside match scrutinees
  _matchDepth :: Int,                     -- ^ Maximum nesting level of matches
  _auxDepth :: Int,                       -- ^ Maximum nesting level of auxiliary functions (lambdas used as arguments)
  _fixStrategy :: FixpointStrategy,       -- ^ How to generate terminating fixpoints
  _polyRecursion :: Bool,                 -- ^ Enable polymorphic recursion?
  _predPolyRecursion :: Bool,             -- ^ Enable recursion polymorphic in abstract predicates?
  _abduceScrutinees :: Bool,              -- ^ Should we match eagerly on all unfolded variables?
  _unfoldLocals :: Bool,                  -- ^ Unfold binders introduced by matching (to use them in match abduction)?
  _partialSolution :: Bool,               -- ^ Should implementations that only cover part of the input space be accepted?
  _incrementalChecking :: Bool,           -- ^ Solve subtyping constraints during the bottom-up phase
  _consistencyChecking :: Bool,           -- ^ Check consistency of function's type with the goal before exploring arguments?
  _splitMeasures :: Bool,                 -- ^ Split subtyping constraints between datatypes into constraints over each measure
  _context :: RWProgram -> RWProgram,       -- ^ Context in which subterm is currently being generated (used only for logging and symmetry reduction)
  _useMemoization :: Bool,                -- ^ Should enumerated terms be memoized?
  _symmetryReduction :: Bool,             -- ^ Should partial applications be memoized to check for redundancy?
  _sourcePos :: SourcePos,                -- ^ Source position of the current goal
  _explorerLogLevel :: Int,                -- ^ How verbose logging is
  _intersectStrategy :: IntersectStrategy,
  _intersectAllMustCheck :: Bool -- ^ Should all worlds check? (default: True)
}

makeLenses ''ExplorerParams

-- | Parameters for template exploration
defaultExplorerParams = ExplorerParams {
  _eGuessDepth = 3,
  _scrutineeDepth = 1,
  _matchDepth = 2,
  _auxDepth = 1,
  _fixStrategy = AllArguments,
  _polyRecursion = True,
  _predPolyRecursion = False,
  _abduceScrutinees = True,
  _unfoldLocals = False,
  _partialSolution = False,
  _incrementalChecking = False,
  _consistencyChecking = False,
  _splitMeasures = True,
  _useMemoization = False,
  _symmetryReduction = False,
  _context = id,
  _sourcePos = noPos,
  _explorerLogLevel = 0,
  _intersectStrategy = InferMedian,
  _intersectAllMustCheck = True
}

-- | State of program exploration
data ExplorerState = ExplorerState {
  _typingState :: TypingState,                     -- ^ Type-checking state
  _auxGoals :: [AuxGoal],                          -- ^ Subterms to be synthesized independently
  _solvedAuxGoals :: Map Id RWProgram,              -- Synthesized auxiliary goals, to be inserted into the main program
  _lambdaLets :: Map Id ([Environment], RWProgram),   -- ^ Local bindings to be checked upon use (in type checking mode)
  _symbolUseCount :: Map Id Int                    -- ^ Number of times each symbol has been used in the program so far
} deriving (Eq, Ord)

makeLenses ''ExplorerState

-- | Key in the memoization store
data MemoKey = MemoKey {
  keyTypeArity :: Int,
  keyLastShape :: SType,
  keyState :: ExplorerState,
  keyDepth :: Int
} deriving (Eq, Ord)


-- | Memoization store
type Memo = Map MemoKey [(RProgram, ExplorerState)]

newtype PartialKey = PartialKey { pKeyContext :: RProgram } deriving (Eq, Ord)

type PartialMemo = Map PartialKey (Map RProgram (Int, Environment))
-- | Persistent state accross explorations
data PersistentState = PersistentState {
  _termMemo :: Memo,
  _partialFailures :: PartialMemo,
  _typeErrors :: [ErrorMessage]
}

makeLenses ''PersistentState

-- | Computations that explore program space, parametrized by the the horn solver @s@
type Explorer s = StateT ExplorerState (
                    ReaderT (ExplorerParams, TypingParams, Reconstructor s) (
                    LogicT (StateT PersistentState s)))

-- | This type encapsulates the 'reconstructTopLevel' function of the type checker,
-- which the explorer calls for auxiliary goals
-- newtype Reconstructor s = Reconstructor (Goal -> Explorer s RWProgram)
newtype Reconstructor s = Reconstructor (AuxGoal -> Explorer s RWProgram)