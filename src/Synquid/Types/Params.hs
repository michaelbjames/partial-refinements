{-# LANGUAGE DeriveDataTypeable #-}

module Synquid.Types.Params where

import Data.Data

-- | Choices for the type of terminating fixpoint operator
data FixpointStrategy =
    DisableFixpoint   -- ^ Do not use fixpoint
  | FirstArgument     -- ^ Fixpoint decreases the first well-founded argument
  | AllArguments      -- ^ Fixpoint decreases the lexicographical tuple of all well-founded argument in declaration order
  | Nonterminating    -- ^ Fixpoint without termination check

-- | Choices for the order of e-term enumeration
data PickSymbolStrategy = PickDepthFirst | PickInterleave

-- | How to deal with intersections at Var rule sites?
data IntersectStrategy
    = -- | Try to check with only one of the intersected types
      EitherOr
    | -- | Use the Laurent BCD subtyping rule for intersection types.
      LaurentBCD
    | -- | Like LaurentBCD, but creates constraints through guarded subtypes
      GuardedPowerset
    deriving (Data, Eq, Ord, Show)