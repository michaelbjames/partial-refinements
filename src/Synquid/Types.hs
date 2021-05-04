{-# LANGUAGE TemplateHaskell, FlexibleContexts, TupleSections, DeriveDataTypeable #-}
module Synquid.Types where

import Data.Data

-- | How to deal with intersections at Var rule sites?
data IntersectStrategy =
    EitherOr         -- ^ Try to check with only one of the intersected types
  | InferMedian      -- ^ Find some supertype that is not an intersection itself
  | LaurentBCD       -- ^ Use the Laurent BCD subtyping rule for intersection types.
  | AlgorithmicLaurent  -- ^ Like Laurent BCD, but on functions, build up co-domain checks to avoid a powerset
  | GuardedPowerset  -- ^ Like LaurentBCD, but creates constraints through guarded subtypes
  deriving (Data, Eq, Ord, Show)