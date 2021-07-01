{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module Synquid.Types.Program where

import Synquid.Types.Error
import Synquid.Util
import Synquid.Types.Type
import Synquid.Types.Logic

import Control.Applicative
import Control.Lens
import Data.Data
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

{- Program terms -}

-- | One case inside a pattern match expression
data Case t = Case
    { -- | Constructor name
      constructor :: Id
    , -- | Bindings for constructor arguments
      argNames :: [Id]
    , -- | Result of the match in this case
      expr :: Program t
    }
    deriving (Show, Eq, Ord, Functor, Foldable)

-- | Program skeletons parametrized by information stored symbols, conditionals, and by node types
data BareProgram t
    = -- | Symbol (variable or constant)
      PSymbol Id
    | -- | Function application
      PApp (Program t) (Program t)
    | -- | Lambda abstraction
      PFun Id (Program t)
    | -- | Conditional
      PIf (Program t) (Program t) (Program t)
    | -- | Pattern match on datatypes
      PMatch (Program t) [Case t]
    | -- | Fixpoint
      PFix [Id] (Program t)
    | -- | Let binding
      PLet Id (Program t) (Program t)
    | -- | Hole (program to fill in)
      PHole
    | -- | Error
      PErr
    deriving (Show, Eq, Ord, Functor, Foldable)

-- | Programs annotated with types
data Program t = Program
    { content :: BareProgram t
    , typeOf :: t
    }
    deriving (Show, Functor, Foldable)

instance Eq (Program t) where
    (==) (Program l _) (Program r _) = l == r

instance Ord (Program t) where
    (<=) (Program l _) (Program r _) = l <= r

-- | Untyped programs
type UProgram = Program RType

-- | Refinement-typed programs
type RProgram = Program RType

-- | Program with a set of types, from the worlds.
type RWProgram = Program TypeVector

-- | User-defined datatype representation
data DatatypeDef = DatatypeDef
    { -- | Type parameters
      _typeParams :: [Id]
    , -- | Signatures of predicate parameters
      _predParams :: [PredSig]
    , -- | For each predicate parameter, whether it is contravariant
      _predVariances :: [Bool]
    , -- | Constructor names
      _constructors :: [Id]
    , -- | Name of the measure that serves as well founded termination metric
      _wfMetric :: Maybe Id
    }
    deriving (Show, Eq, Ord)

makeLenses ''DatatypeDef

-- | One case in a measure definition: constructor name, arguments, and body
data MeasureCase = MeasureCase Id [Id] Formula
    deriving (Show, Eq, Ord)

type MeasureDefaults = [(Id, Sort)]

-- | User-defined measure function representation
data MeasureDef = MeasureDef
    { _inSort :: Sort
    , _outSort :: Sort
    , _definitions :: [MeasureCase]
    , _constantArgs :: MeasureDefaults
    , _postcondition :: Formula
    }
    deriving (Show, Eq, Ord)

makeLenses ''MeasureDef

type ArgMap = Map Id [Set Formula] -- All possible constant arguments of measures with multiple arguments

-- | Constructor signature: name and type
data ConstructorSig = ConstructorSig Id RType
    deriving (Show, Eq)

constructorName (ConstructorSig name _) = name

data BareDeclaration
    = -- | Type name, variables, and definition
      TypeDecl Id [Id] RType
    | -- | Function name and signature
      FuncDecl Id RSchema
    | -- | Datatype name, type parameters, predicate parameters, and constructor definitions
      DataDecl Id [Id] [(PredSig, Bool)] [ConstructorSig]
    | -- | Measure name, input sort, output sort, postcondition, definition cases, and whether this is a termination metric
      MeasureDecl Id Sort Sort Formula [MeasureCase] MeasureDefaults Bool
    | -- | Module-level predicate
      PredDecl PredSig
    | -- | Qualifiers
      QualifierDecl [Formula]
    | -- | Mutual recursion group
      MutualDecl [Id]
    | -- | Inline predicate
      InlineDecl Id [Id] Formula
    | -- | Name and template for the function to reconstruct
      SynthesisGoal Id UProgram
    deriving (Show, Eq)

type Declaration = Pos BareDeclaration

isSynthesisGoal (Pos _ (SynthesisGoal _ _)) = True
isSynthesisGoal _ = False
