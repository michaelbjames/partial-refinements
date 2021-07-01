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

import Data.List.Extra

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

{- Qualifiers -}

-- | Search space for valuations of a single unknown
data QSpace = QSpace {
    _qualifiers :: [Formula],         -- ^ Qualifiers
    _maxCount :: Int                  -- ^ Maximum number of qualifiers in a valuation
  } deriving (Show, Eq, Ord)

makeLenses ''QSpace

emptyQSpace = QSpace [] 0


toSpace mbN quals = let quals' = nubOrd quals in
  case mbN of
    Nothing -> QSpace quals' (length quals')
    Just n -> QSpace quals' n

-- | Mapping from unknowns to their search spaces
type QMap = Map Id QSpace

type ExtractAssumptions = Formula -> Set Formula

{- Solutions -}

-- | Valuation of a predicate unknown as a set of qualifiers
type Valuation = Set Formula

-- | Mapping from predicate unknowns to their valuations
type Solution = Map Id Valuation


dontCare = "_"
valueVarName = "_v"


ftrue = BoolLit True
ffalse = BoolLit False
boolVar = Var BoolS
valBool = boolVar valueVarName
intVar = Var IntS
valInt = intVar valueVarName
vartVar n = Var (VarS n)
valVart n = vartVar n valueVarName
setVar s = Var (SetS (VarS s))
valSet s = setVar s valueVarName
fneg = Unary Neg
fnot = Unary Not
(|*|) = Binary Times
(|+|) = Binary Plus
(|-|) = Binary Minus
(|=|) = Binary Eq
(|/=|) = Binary Neq
(|<|) = Binary Lt
(|<=|) = Binary Le
(|>|) = Binary Gt
(|>=|) = Binary Ge
(|&|) = Binary And
(|||) = Binary Or
(|=>|) = Binary Implies
(|<=>|) = Binary Iff

(/+/) = Binary Union
(/*/) = Binary Intersect
(/-/) = Binary Diff
fin = Binary Member
(/<=/) = Binary Subset

infixl 9 |*|
infixl 8 |+|, |-|, /+/, /-/, /*/
infixl 7 |=|, |/=|, |<|, |<=|, |>|, |>=|, /<=/
infixl 6 |&|, |||
infixr 5 |=>|
infix 4 |<=>|



{- Solution Candidates -}

-- | Solution candidate
data Candidate = Candidate {
    solution :: Solution,
    validConstraints :: Set Formula,
    invalidConstraints :: Set Formula,
    label :: String
  } deriving (Show)

initialCandidate = Candidate Map.empty Set.empty Set.empty "0"

instance Eq Candidate where
  (==) c1 c2 = Map.filter (not . Set.null) (solution c1) == Map.filter (not . Set.null) (solution c2) &&
               validConstraints c1 == validConstraints c2 &&
               invalidConstraints c1 == invalidConstraints c2

instance Ord Candidate where
  (<=) c1 c2 = Map.filter (not . Set.null) (solution c1) <= Map.filter (not . Set.null) (solution c2) &&
               validConstraints c1 <= validConstraints c2 &&
               invalidConstraints c1 <= invalidConstraints c2
