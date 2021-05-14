{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module Synquid.Types.Logic where

import Control.Applicative
import Control.Lens
import Data.Data
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Synquid.Types.Error
import Synquid.Util

{- Formulas of the refinement logic -}

-- | Unary operators
data UnOp = Neg | Not
    deriving (Show, Eq, Ord)

-- | Binary operators
data BinOp
    = Times
    | Plus
    | Minus
    | Eq
    | Neq
    | Lt
    | Le
    | Gt
    | Ge
    | And
    | Or
    | Implies
    | Iff
    | Union
    | Intersect
    | Diff
    | Member
    | Subset
    deriving (Show, Eq, Ord)

-- | Variable substitution
type Substitution = Map Id Formula

-- | Formulas of the refinement logic
data Formula
    = -- | Boolean literal
      BoolLit Bool
    | -- | Integer literal
      IntLit Integer
    | -- | Set literal ([1, 2, 3])
      SetLit Sort [Formula]
    | -- | Input variable (universally quantified first-order variable)
      Var Sort Id
    | -- | Predicate unknown (with a pending substitution)
      Unknown Substitution Id
    | -- | Unary expression
      Unary UnOp Formula
    | -- | Binary expression
      Binary BinOp Formula Formula
    | -- | If-then-else expression
      Ite Formula Formula Formula
    | -- | Logic function application
      Pred Sort Id [Formula]
    | -- | Constructor application
      Cons Sort Id [Formula]
    | -- | Universal quantification
      All Formula Formula
    deriving (Show, Eq, Ord)

-- | Sorts
data Sort
    = BoolS
    | IntS
    | VarS Id
    | DataS Id [Sort]
    | SetS Sort
    | AnyS
    deriving (Show, Eq, Ord)

data PredSig = PredSig
    { predSigName :: Id
    , predSigArgSorts :: [Sort]
    , predSigResSort :: Sort
    }
    deriving (Show, Eq, Ord)
