{-# LANGUAGE FlexibleInstances, UndecidableInstances, FlexibleContexts #-}

module Synquid.Pretty (   
  -- * Interface
  Pretty (..),
  Doc,
  renderPretty,
  putDoc,
  -- * Basic documents  
  empty,
  isEmpty,
  text,
  linebreak,
  semi,
  lbrace, rbrace,
  -- * Combinators
  option,
  optionMaybe,  
  (<+>), ($+$), (<>),
  hcat,
  vcat,
  hsep,
  vsep,
  punctuate,
  tupled,
  -- * Enclosing
  commaSep,  
  parens,
  condParens,
  dquotes,
  brackets,
  braces,
  angles,
  spaces,
  -- * Indentation
  nest,
  -- * Structures
  hMapDoc,
  vMapDoc,
  -- * Other
  programDoc,
  candidateDoc,
  -- * Counting
  typeNodeCount,
  programNodeCount
) where

import Synquid.Logic
import Synquid.Program
import Synquid.SMTSolver
import Synquid.Util

import Text.PrettyPrint.ANSI.Leijen hiding ((<+>), (<$>), hsep, vsep)
import qualified Text.PrettyPrint.ANSI.Leijen as L
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map, (!))
import qualified Data.Bimap as BMap
import Data.Bimap (Bimap)

import Control.Lens

infixr 5 $+$
infixr 6 <+>
  
-- | Is document empty?
isEmpty d = case renderCompact d of
  SEmpty -> True
  _ -> False
  
-- | Separate two documents by space if both are nonempty  
doc1 <+> doc2 = if isEmpty doc1
  then doc2
  else if isEmpty doc2
    then doc1
    else doc1 L.<+> doc2
    
-- | Separate two documents by linebreak if both are nonempty    
doc1 $+$ doc2 = if isEmpty doc1
  then doc2
  else if isEmpty doc2
    then doc1
    else doc1 L.<$> doc2

-- | Separate by spaces
hsep = foldr (<+>) empty    
-- | Separate by new lines
vsep = foldr ($+$) empty    
-- | Separate by commas
commaSep = hsep . punctuate comma

-- | Enclose in spaces    
spaces d = space <> d <> space
-- | Conditionally enclose in parentheses  
condParens b doc = if b then parens doc else doc
      
-- | Conditionally produce a doc
option b doc = if b then doc else empty

-- | Convert a 'Just' value to doc
optionMaybe mVal toDoc = case mVal of
  Nothing -> empty
  Just val -> toDoc val
    
entryDoc keyDoc valDoc (k, v) = nest 2 $ (keyDoc k  <+> text "->") <+> valDoc v 
  
hMapDoc :: (k -> Doc) -> (v -> Doc) -> Map k v -> Doc    
hMapDoc keyDoc valDoc m = brackets (commaSep (map (entryDoc keyDoc valDoc) (Map.toList m)))  
  
vMapDoc :: (k -> Doc) -> (v -> Doc) -> Map k v -> Doc  
vMapDoc keyDoc valDoc m = vsep $ map (entryDoc keyDoc valDoc) (Map.toList m)

{- Formulas -}

instance Pretty Sort where
  pretty IntS = text "int"
  pretty BoolS = text "bool"    
  pretty (SetS el) = text "bet" <+> pretty el
  pretty (UninterpretedS name) = text name

instance Show Sort where
  show = show . pretty    

instance Pretty UnOp where
  pretty Neg = text "-"
  pretty Not = text "!"

instance Show UnOp where
  show = show . pretty
  
instance Pretty BinOp where
  pretty Times = text "*"
  pretty Plus = text "+"
  pretty Minus = text "-"
  pretty Eq = text "=="
  pretty Neq = text "/="
  pretty Lt = text "<"
  pretty Le = text "<="
  pretty Gt = text ">"
  pretty Ge = text ">="
  pretty And = text "&&"
  pretty Or = text "||"
  pretty Implies = text "==>"  
  pretty Iff = text "<==>"  
  pretty Union = text "+"
  pretty Intersect = text "*"
  pretty Diff = text "-"
  pretty Member = text "in"
  pretty Subset = text "<="
  
instance Show BinOp where
  show = show . pretty  

-- | Binding power of a formula
power :: Formula -> Int
power (Unary _ _) = 6
power (Binary op _ _) 
  | op `elem` [Times] = 5
  | op `elem` [Plus, Minus] = 4
  | op `elem` [Eq, Neq, Lt, Le, Gt, Ge] = 3
  | op `elem` [And, Or] = 2
  | op `elem` [Implies] = 1
  | op `elem` [Iff] = 0
power _ = 7

-- | Pretty-printed formula  
fmlDoc :: Formula -> Doc
fmlDoc fml = fmlDocAt (-1) fml

-- | 'fmlDocAt' @n fml@ : print @expr@ in a context with binding power @n@
fmlDocAt :: Int -> Formula -> Doc
fmlDocAt n fml = condParens (n' <= n) (
  case fml of
    BoolLit b -> pretty b
    IntLit i -> squotes $ pretty i
    SetLit _ elems -> braces $ commaSep $ map pretty elems
    Var s name -> text name -- <> text ":" <> pretty  s
    Unknown s name -> if Map.null s then text name else hMapDoc pretty pretty s <> text name
    Unary op e -> pretty op <> fmlDocAt n' e
    Binary op e1 e2 -> fmlDocAt n' e1 <+> pretty op <+> fmlDocAt n' e2
    Measure b name arg -> text name <+> pretty arg -- text name <> text ":" <> pretty  b <+> pretty arg
  )
  where
    n' = power fml
    
instance Pretty Formula where pretty e = fmlDoc e

instance Show Formula where
  show = show . pretty  
    
instance Pretty Valuation where
  pretty val = braces $ commaSep $ map pretty $ Set.toList val
  
instance Pretty Solution where
  pretty = hMapDoc text pretty
  
instance Pretty QSpace where
  pretty space = braces $ commaSep $ map pretty $ view qualifiers space
  
instance Pretty QMap where
  pretty = vMapDoc text pretty  
  
instance Pretty BaseType where
  pretty IntT = text "Int"
  pretty BoolT = text "Bool"    
  pretty (TypeVarT name) = text name -- if Map.null s then text name else hMapDoc pretty pretty s <> text name
  pretty (DatatypeT name) = text name
  
instance Show BaseType where
  show = show . pretty
    
caseDoc :: (TypeSkeleton r -> Doc) -> Case r -> Doc
caseDoc tdoc cas = text (constructor cas) <+> hsep (map text $ argNames cas) <+> text "->" <+> programDoc tdoc (expr cas) 

programDoc :: (TypeSkeleton r -> Doc) -> Program r -> Doc
programDoc tdoc (Program p typ) = let 
    pDoc = programDoc tdoc
    withType doc = let td = tdoc typ in (option (not $ isEmpty td) $ braces td) <+> doc
  in case p of
    PSymbol s -> withType $ text s
    PApp f x -> parens (pDoc f <+> pDoc x)
    PFun x e -> nest 2 $ withType (text "\\" <> text x <+> text ".") $+$ pDoc e
    PIf c t e -> nest 2 $ withType (text "if" <+> pretty c) $+$ (text "then" <+> pDoc t) $+$ (text "else" <+> pDoc e)
    PMatch l cases -> nest 2 $ withType (text "match" <+> pDoc l <+> text "with") $+$ vsep (map (caseDoc tdoc) cases)
    PFix fs e -> nest 2 $ withType (text "fix" <+> hsep (map text fs) <+> text ".") $+$ pDoc e

instance (Pretty (TypeSkeleton r)) => Pretty (Program r) where
  pretty = programDoc pretty
  
instance (Pretty (TypeSkeleton r)) => Show (Program r) where
  show = show . pretty
  
prettySType :: SType -> Doc
prettySType (ScalarT base args _) = pretty base <+> hsep (map (parens . pretty) args)
prettySType (FunctionT _ t1 t2) = parens (pretty t1 <+> text "->" <+> pretty t2)

instance Pretty SType where
  pretty = prettySType
  
instance Show SType where
 show = show . pretty
  
prettyType :: RType -> Doc
prettyType (ScalarT base args (BoolLit True)) = pretty base <+> hsep (map (parens . pretty) args)
prettyType (ScalarT base args fml) = braces (pretty base <+> hsep (map (parens . pretty) args) <> text "|" <> pretty fml)
prettyType (FunctionT x t1 t2) = parens (text x <> text ":" <> pretty t1 <+> text "->" <+> pretty t2)

instance Pretty RType where
  pretty = prettyType
  
instance Show RType where
 show = show . pretty  
 
prettySSchema :: SSchema -> Doc
prettySSchema (Monotype t) = pretty t
prettySSchema (Forall a t) = angles (text a) <+> pretty t
 
instance Pretty SSchema where
  pretty sch = case sch of
    Monotype t -> pretty t
    Forall a sch' -> angles (text a) <+> pretty sch'
    
instance Show SSchema where
 show = show . pretty      
 
instance Pretty RSchema where
  pretty sch = case sch of
    Monotype t -> pretty t
    Forall a sch' -> angles (text a) <+> pretty sch'
    
instance Show RSchema where
  show = show . pretty       
 
instance Pretty TypeSubstitution where
  pretty = hMapDoc text pretty  
    
prettyBinding (name, typ) = text name <+> text "::" <+> pretty typ

prettyAssumptions env = commaSep (map pretty (Set.toList $ env ^. assumptions) ++ map (pretty . fnot) (Set.toList $ env ^. negAssumptions)) 
-- prettyBindings env = commaSep (map pretty (Set.toList $ Map.keysSet (allSymbols env) Set.\\ (env ^. constants))) 
prettyBindings env = hMapDoc pretty pretty (removeDomain (env ^. constants) (allSymbols env))
-- prettyBindings env = empty
  
instance Pretty Environment where
  pretty env = prettyBindings env <+> commaSep (map pretty (Set.toList $ env ^. assumptions) ++ map (pretty . fnot) (Set.toList $ env ^. negAssumptions))
  
prettyConstraint :: Constraint -> Doc  
prettyConstraint (Subtype env t1 t2) = prettyBindings env <+> prettyAssumptions env <+> text "|-" <+> pretty t1 <+> text "<:" <+> pretty t2
prettyConstraint (WellFormed env t) = prettyBindings env <+> text "|-" <+> pretty t
prettyConstraint (WellFormedCond env c) = prettyBindings env <+> text "|-" <+> pretty c
  
instance Pretty Constraint where
  pretty = prettyConstraint
  
instance Pretty Candidate where
  pretty (Candidate sol valids invalids label) = text label <> text ":" <+> pretty sol <+> parens (pretty (Set.size valids) <+> pretty (Set.size invalids))    
    
candidateDoc :: RProgram -> Candidate -> Doc
candidateDoc prog (Candidate sol _ _ label) = text label <> text ":" <+> programDoc pretty (programApplySolution sol prog)
    
{- AST node counting -}

-- | 'fmlNodeCount' @fml@ : size of @fml@ (in AST nodes)
fmlNodeCount :: Formula -> Int
fmlNodeCount (SetLit _ args) = 1 + sum (map fmlNodeCount args)
fmlNodeCount (Unary _ e) = 1 + fmlNodeCount e
fmlNodeCount (Binary _ l r) = 1 + fmlNodeCount l + fmlNodeCount r
fmlNodeCount (Measure _ _ e) = 1 + fmlNodeCount e
fmlNodeCount _ = 1

-- | 'typeNodeCount' @t@ : cumulative size of all refinements in @t@
typeNodeCount :: RType -> Int 
typeNodeCount (ScalarT _ tArgs fml) = fmlNodeCount fml + sum (map typeNodeCount tArgs)
typeNodeCount (FunctionT _ tArg tRes) = typeNodeCount tArg + typeNodeCount tRes 

-- | 'programNodeCount' @p@ : size of @p@ (in AST nodes)
programNodeCount :: RProgram -> Int
programNodeCount (Program p _) = case p of 
  PSymbol _ -> 1
  PApp e1 e2 -> 1 + programNodeCount e1 + programNodeCount e2
  PFun _ e -> 1 + programNodeCount e 
  PIf c e1 e2 -> 1 + fmlNodeCount c + programNodeCount e1 + programNodeCount e2
  PMatch e cases -> 1 + programNodeCount e + sum (map (\(Case _ _ e) -> programNodeCount e) cases)
  PFix _ e -> 1 + programNodeCount e
