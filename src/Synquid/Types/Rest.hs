{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module Synquid.Types.Rest where

import Synquid.Util
import Synquid.Types.Error
import Synquid.Types.Logic
import Synquid.Types.Type
import Synquid.Types.Program

import Control.Applicative
import Control.Lens
import Data.Data
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set


-- | Constraints generated during formula resolution
data SortConstraint
    = SameSort Sort Sort -- Two sorts must be the same
    | IsOrd Sort -- Sort must have comparisons

{- Evaluation environment -}

-- | Typing environment
data Environment = Environment
    { -- | Variable part:
      _symbols :: Map Int (Map Id RSchema), -- | Bound type variables
      _boundTypeVars :: [Id], -- | Argument sorts of bound abstract refinements
      _boundPredicates :: [PredSig], -- | Unknown assumptions
      _assumptions :: Set Formula, -- | For polymorphic recursive calls, the shape their types must have
      _shapeConstraints :: Map Id SType, -- | Program terms that has already been scrutinized
      _usedScrutinees :: [RProgram], -- | In eager match mode, datatype variables that can be scrutinized
      _unfoldedVars :: Set Id, -- | Subset of symbols that are let-bound
      _letBound :: Set Id, -- | Used in GuardedSubtype intersection strategy. These formulae are only (positive, negative)
      _subtypeGuards :: (Set Formula, Set Formula), -- | Subset of symbols that are constants
      -- | Constant part:
      _constants :: Set Id, -- | Datatype definitions
      _datatypes :: Map Id DatatypeDef, -- | Signatures (resSort:argSorts) of module-level logic functions (measures, predicates)
      _globalPredicates :: Map Id [Sort], -- | Measure definitions
      _measures :: Map Id MeasureDef, -- | Type synonym definitions
      _typeSynonyms :: Map Id ([Id], RType), -- | Unresolved types of components (used for reporting specifications with macros)
      _unresolvedConstants :: Map Id RSchema
    }
    deriving (Show)

makeLenses ''Environment

instance Eq Environment where
    (==) e1 e2 = (e1 ^. symbols) == (e2 ^. symbols) && (e1 ^. assumptions) == (e2 ^. assumptions)

instance Ord Environment where
    (<=) e1 e2 = (e1 ^. symbols) <= (e2 ^. symbols) && (e1 ^. assumptions) <= (e2 ^. assumptions)

-- | Empty environment
emptyEnv =
    Environment
        { _symbols = Map.empty
        , _boundTypeVars = []
        , _boundPredicates = []
        , _assumptions = Set.empty
        , _shapeConstraints = Map.empty
        , _usedScrutinees = []
        , _unfoldedVars = Set.empty
        , _letBound = Set.empty
        , _subtypeGuards = (Set.empty, Set.empty)
        , _constants = Set.empty
        , _globalPredicates = Map.empty
        , _datatypes = Map.empty
        , _measures = Map.empty
        , _typeSynonyms = Map.empty
        , _unresolvedConstants = Map.empty
        }

{- Misc -}

-- | Typing constraints
data Constraint
    = Subtype Environment RType RType Bool Id
    | WellFormed Environment RType
    | WellFormedCond Environment Formula
    | WellFormedMatchCond Environment Formula
    | WellFormedPredicate Environment [Sort] Id
    deriving (Show, Eq, Ord)

-- | Synthesis goal
data Goal = Goal
    { -- | Function name
      gName :: Id
    , -- | Enclosing environment
      gEnvironment :: Environment
    , -- | Specification
      gSpec :: RSchema
    , -- | Implementation template
      gImpl :: UProgram
    , -- | Maximum level of auxiliary goal nesting allowed inside this goal
      gDepth :: Int
    , -- | Source Position,
      gSourcePos :: SourcePos
    , -- | Synthesis flag (false implies typechecking only)
      gSynthesize :: Bool
    }
    deriving (Show, Eq, Ord)

type World = (Environment, RType)
