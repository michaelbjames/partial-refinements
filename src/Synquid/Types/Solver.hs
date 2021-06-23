{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}

module Synquid.Types.Solver where

import Synquid.Types.Rest
import Synquid.Types.Logic
import Synquid.Types.Program
import Synquid.Types.Params
import Synquid.Types.Error
import Synquid.Types.Type
import Synquid.Util

import Control.Lens
import Data.Map
import qualified Data.Set as Set
import Text.PrettyPrint.ANSI.Leijen
import Control.Monad.Logic
import Control.Monad.State ( StateT )
import Control.Monad.Reader
import Control.Monad.Except

{- Interface -}

-- | Parameters of type constraint solving
data TypingParams = TypingParams {
  _condQualsGen :: Environment -> [Formula] -> QSpace,              -- ^ Qualifier generator for conditionals
  _matchQualsGen :: Environment -> [Formula] -> QSpace,             -- ^ Qualifier generator for match scrutinees
  _typeQualsGen :: Environment -> Formula -> [Formula] -> QSpace,   -- ^ Qualifier generator for types
  _predQualsGen :: Environment -> [Formula] -> [Formula] -> QSpace, -- ^ Qualifier generator for bound predicates
  _tcSolverSplitMeasures :: Bool,
  _tcSolverLogLevel :: Int,    -- ^ How verbose logging is
  _tcIntersection :: IntersectStrategy
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
  _initEnv :: Environment,                      -- ^ Initial environment, used for the measures
  _idCount :: Map String Int,                   -- ^ Number of unique identifiers issued so far
  _isFinal :: Bool,                             -- ^ Has the entire program been seen?
  _topLevelGoals :: [RType],                     -- ^ The top-level goal per world.
  _currentWorldNumOneIdx :: Int,
  -- Temporary state:
  _simpleConstraints :: [Constraint],           -- ^ Typing constraints that cannot be simplified anymore and can be converted to horn clauses or qualifier maps
  _hornClauses :: [(Formula, Id)],              -- ^ Horn clauses generated from subtyping constraints
  _consistencyChecks :: [Formula],              -- ^ Formulas generated from type consistency constraints
  _errorContext :: (SourcePos, Doc)             -- ^ Information to be added to all type errors
}

makeLenses ''TypingState

constraintsForEq = Set.fromList ["a", "u"]

instance Eq TypingState where
  (==) st1 st2 = (restrictDomain constraintsForEq (_idCount st1) == restrictDomain constraintsForEq (_idCount st2)) &&
                  _typeAssignment st1 == _typeAssignment st2 &&
                  _candidates st1 == _candidates st2

instance Ord TypingState where
  (<=) st1 st2 = (restrictDomain constraintsForEq (_idCount st1) <= restrictDomain constraintsForEq (_idCount st2)) &&
                _typeAssignment st1 <= _typeAssignment st2 &&
                _candidates st1 <= _candidates st2

-- | Computations that solve type constraints, parametrized by the the horn solver @s@
type TCSolver s = StateT TypingState (ReaderT TypingParams (ExceptT ErrorMessage s))
