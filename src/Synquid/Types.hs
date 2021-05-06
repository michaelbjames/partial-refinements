{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module Synquid.Types where

import Data.Data

-- | How to deal with intersections at Var rule sites?
data IntersectStrategy
    = -- | Try to check with only one of the intersected types
      EitherOr
    | -- | Find some supertype that is not an intersection itself
      InferMedian
    | -- | Use the Laurent BCD subtyping rule for intersection types.
      LaurentBCD
    | -- | Like Laurent BCD, but on functions, build up co-domain checks to avoid a powerset
      AlgorithmicLaurent
    | -- | Like LaurentBCD, but creates constraints through guarded subtypes
      GuardedPowerset
    deriving (Data, Eq, Ord, Show)