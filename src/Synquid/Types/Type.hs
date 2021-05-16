{-# LANGUAGE FlexibleContexts #-}

module Synquid.Types.Type where

import Synquid.Types.Error
import Synquid.Util
import Synquid.Types.Logic

import Control.Applicative
import Control.Lens
import Data.Data
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

{- Type skeletons -}

data BaseType r = BoolT | IntT | DatatypeT Id [TypeSkeleton r] [r] | TypeVarT Substitution Id
    deriving (Show, Eq, Ord)

-- | Type skeletons (parametrized by refinements)
data TypeSkeleton r
    = ScalarT (BaseType r) r
    | FunctionT Id (TypeSkeleton r) (TypeSkeleton r)
    | LetT Id (TypeSkeleton r) (TypeSkeleton r)
    | AndT (TypeSkeleton r) (TypeSkeleton r)
    | UnionT (TypeSkeleton r) (TypeSkeleton r)
    | AnyT
    deriving (Show, Eq, Ord)

-- | Polymorphic type skeletons (parametrized by refinements)
data SchemaSkeleton r
    = Monotype (TypeSkeleton r)
    | ForallT Id (SchemaSkeleton r) -- Type-polymorphic
    | ForallP PredSig (SchemaSkeleton r) -- Predicate-polymorphic
    deriving (Show, Eq, Ord)

{- Refinement types -}

-- | Unrefined typed
type SType = TypeSkeleton ()

-- | Refined types
type RType = TypeSkeleton Formula

-- | Unrefined schemas
type SSchema = SchemaSkeleton ()

-- | Refined schemas
type RSchema = SchemaSkeleton Formula

-- | Mapping from type variables to types
type TypeSubstitution = Map Id RType