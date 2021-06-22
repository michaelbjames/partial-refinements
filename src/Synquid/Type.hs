-- | Refinement Types
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Synquid.Type where

import Synquid.Logic
import Synquid.Tokens
import Synquid.Util
import Synquid.Types.Logic
import Synquid.Types.Type

import Data.Maybe
import Data.Either
import Data.List
import Data.Function
import Data.List.Extra
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

import Control.Arrow hiding ((|||))
import Control.Monad
import Control.Monad.State
import Control.Lens hiding (set)
import Development.Placeholders
import GHC.Stack


btEq :: BaseType a -> BaseType a -> Bool
btEq BoolT BoolT = True
btEq IntT IntT = True
btEq (TypeVarT _ x) (TypeVarT _ y) = True -- TODO: We could equate inequivalent types!
btEq (DatatypeT name1 args1 _) (DatatypeT name2 args2 _) =
  (name1 == name2) &&
  (length args1) == (length args2) &&
  (foldr (\(al, ar) -> (&&) (arrowEq al ar)) True (zip args1 args2))
btEq _ _ = False

arrowEq :: TypeSkeleton a -> TypeSkeleton a -> Bool
arrowEq (ScalarT bt1 _) (ScalarT bt2 _) = btEq bt1 bt2
arrowEq (FunctionT x arg1 ret1) (FunctionT y arg2 ret2) =
  arrowEq arg1 arg2 && arrowEq ret1 ret2
arrowEq (LetT{}) (LetT{}) = error "arrowEq on contextual type"
arrowEq (UnionT{}) (UnionT{}) = error "arrowEq on Union type"
arrowEq (AndT l r) (AndT l' r') = arrowEq l l' && arrowEq r r'
arrowEq AnyT AnyT = True
arrowEq _ _ = False

contextual x tDef (FunctionT y tArg tRes) = FunctionT y (contextual x tDef tArg) (contextual x tDef tRes)
contextual _ _ AnyT = AnyT
contextual x tDef t = LetT x tDef t

isScalarType (ScalarT _ _) = True
-- isScalarType (LetT _ _ t) = isScalarType t
isScalarType (LetT _ _ _) = True
isScalarType _ = False

baseTypeOf :: HasCallStack => TypeSkeleton r -> BaseType r
baseTypeOf (ScalarT baseT _) = baseT
baseTypeOf (LetT _ _ t) = baseTypeOf t
baseTypeOf _ = error "baseTypeOf: applied to a function type"

isFunctionType (FunctionT _ _ _) = True
-- isFunctionType (LetT _ _ t) = isFunctionType t
isFunctionType _ = False

argName (FunctionT x _ _) = x
argType (FunctionT _ t _) = t
resType (FunctionT _ _ t) = t

isIntersection (AndT _ _) = True
isIntersection _ = False

isContextual LetT{} = True
isContextual _ = False

checkWellFormedIntersection t = let
  topLevel = intersectionToList t
  in
    if or $ fmap isIntersection topLevel
    then error "There's an intersection not on the top level. Check your type."
    else t

isUnion (UnionT _ _) = True
isUnion _ = False

containsIntersection (AndT _ _) = True
containsIntersection (FunctionT _ arg res) = containsIntersection arg || containsIntersection res
containsIntersection (LetT _ binding bound) = containsIntersection binding || containsIntersection bound
containsIntersection _ = False

intersectionToList (AndT lty rty) = intersectionToList lty ++ intersectionToList rty
intersectionToList x = [x]

listToIntersection [x] = x
listToIntersection xs = foldr1 AndT xs

unionToList (UnionT lty rty) = unionToList lty ++ unionToList rty
unionToList x = [x]

hasAny AnyT = True
hasAny (ScalarT baseT _) = baseHasAny baseT
  where
    baseHasAny (DatatypeT _ tArgs _) = any hasAny tArgs
    baseHasAny _ = False
hasAny (FunctionT _ tArg tRes) = hasAny tArg || hasAny tRes
hasAny (LetT _ tDef tBody) = hasAny tDef || hasAny tBody

-- | Convention to indicate "any datatype" (for synthesizing match scrtuinees)
anyDatatype = ScalarT (DatatypeT dontCare [] []) ftrue

toSort :: BaseType t -> Sort
toSort BoolT = BoolS
toSort IntT = IntS
toSort (DatatypeT name tArgs _) = DataS name (map (toSort . baseTypeOf) tArgs)
toSort (TypeVarT _ name) = VarS name

fromSort :: Sort -> TypeSkeleton Formula
fromSort = flip refineSort ftrue

refineSort :: Sort -> Formula -> TypeSkeleton Formula
refineSort BoolS f = ScalarT BoolT f
refineSort IntS f = ScalarT IntT f
refineSort (VarS name) f = ScalarT (TypeVarT Map.empty name) f
refineSort (DataS name sArgs) f = ScalarT (DatatypeT name (map fromSort sArgs) []) f
refineSort (SetS s) f = ScalarT dt f
  where
    dt = DatatypeT setTypeName [fromSort s] []
    tvar = ScalarT (TypeVarT Map.empty setTypeVar) f
refineSort AnyS f = AnyT

typeIsData :: TypeSkeleton r -> Bool
typeIsData (ScalarT DatatypeT{} _) = True
typeIsData AndT{} = $(todo "typeIsData andT")
typeIsData _ = False

arity :: TypeSkeleton r -> Int
arity (FunctionT _ _ t) = 1 + arity t
arity (LetT _ _ t) = arity t
arity (AndT l _) = arity l -- these should be the same though.
arity _ = 0


-- TODO: make sure the AnyT case is OK
hasSet :: TypeSkeleton r -> Bool
hasSet (ScalarT (DatatypeT name _ _) _) = name == setTypeName
hasSet (FunctionT _ t1 t2) = hasSet t1 || hasSet t2
hasSet (LetT _ t1 t2) = hasSet t1 || hasSet t2
hasSet (AndT l r) = hasSet l || hasSet r
hasSet _ = False

lastType (FunctionT _ _ tRes) = lastType tRes
lastType (LetT _ _ t) = lastType t
lastType t = t

allArgTypes (AndT l r) = allArgTypes l
allArgTypes (FunctionT x tArg tRes) = tArg : (allArgTypes tRes)
allArgTypes (LetT _ _ t) = allArgTypes t
allArgTypes _ = []

allArgs (ScalarT _ _) = []
allArgs (FunctionT x (ScalarT baseT _) tRes) = (Var (toSort baseT) x) : (allArgs tRes)
allArgs (FunctionT x _ tRes) = (allArgs tRes)
allArgs (LetT _ _ t) = allArgs t

-- | Free variables of a type
varsOfType :: RType -> Set Id
varsOfType (ScalarT baseT fml) = varsOfBase baseT `Set.union` (Set.map varName $ varsOf fml)
  where
    varsOfBase (DatatypeT name tArgs pArgs) = Set.unions (map varsOfType tArgs) `Set.union` (Set.map varName $ Set.unions (map varsOf pArgs))
    varsOfBase _ = Set.empty
varsOfType (FunctionT x tArg tRes) = varsOfType tArg `Set.union` (Set.delete x $ varsOfType tRes)
varsOfType (LetT x tDef tBody) = varsOfType tDef `Set.union` (Set.delete x $ varsOfType tBody)
varsOfType AnyT = Set.empty

-- | Free variables of a type
predsOfType :: RType -> Set Id
predsOfType (ScalarT baseT fml) = predsOfBase baseT `Set.union` predsOf fml
  where
    predsOfBase (DatatypeT name tArgs pArgs) = Set.unions (map predsOfType tArgs) `Set.union` (Set.unions (map predsOf pArgs))
    predsOfBase _ = Set.empty
predsOfType (FunctionT x tArg tRes) = predsOfType tArg `Set.union` predsOfType tRes
predsOfType (LetT x tDef tBody) = predsOfType tDef `Set.union` predsOfType tBody
predsOfType AnyT = Set.empty

varRefinement x s = Var s valueVarName |=| Var s x
isVarRefinement (Binary Eq (Var _ v) (Var _ _)) = v == valueVarName
isVarRefinement _ = False

toMonotype :: SchemaSkeleton r -> TypeSkeleton r
toMonotype (Monotype t) = t
toMonotype (ForallT _ t) = toMonotype t
toMonotype (ForallP _ t) = toMonotype t

boundVarsOf :: SchemaSkeleton r -> [Id]
boundVarsOf (ForallT a sch) = a : boundVarsOf sch
boundVarsOf _ = []

-- | Building types
bool = ScalarT BoolT
bool_ = bool ()
boolAll = bool ftrue

int = ScalarT IntT
int_ = int ()
intAll = int ftrue
nat = int (valInt |>=| IntLit 0)
pos = int (valInt |>| IntLit 0)

vart n = ScalarT (TypeVarT Map.empty n)
vart_ n = vart n ()
vartAll n = vart n ftrue

set n = ScalarT (DatatypeT setTypeName [tvar] [])
  where
    tvar = ScalarT (TypeVarT Map.empty n) ftrue
setAll n = (set n) ftrue

asSortSubst :: TypeSubstitution -> SortSubstitution
asSortSubst = Map.map (toSort . baseTypeOf)

-- | 'typeSubstitute' @t@ : substitute all free type variables in @t@
typeSubstitute :: TypeSubstitution -> RType -> RType
typeSubstitute subst (ScalarT baseT r) = addRefinement substituteBase (sortSubstituteFml (asSortSubst subst) r)
  where
    substituteBase = case baseT of
      TypeVarT varSubst a -> case Map.lookup a subst of
        Just t -> substituteInType (not . (`Map.member` subst)) varSubst $ typeSubstitute subst t
        Nothing -> ScalarT (TypeVarT varSubst a) ftrue
      DatatypeT name tArgs pArgs ->
        let
          tArgs' = map (typeSubstitute subst) tArgs
          pArgs' = map (sortSubstituteFml (asSortSubst subst)) pArgs
        in ScalarT (DatatypeT name tArgs' pArgs') ftrue
      _ -> ScalarT baseT ftrue
typeSubstitute subst (FunctionT x tArg tRes) = FunctionT x (typeSubstitute subst tArg) (typeSubstitute subst tRes)
typeSubstitute subst (LetT x tDef tBody) = LetT x (typeSubstitute subst tDef) (typeSubstitute subst tBody)
typeSubstitute subst (AndT l r) = AndT (typeSubstitute subst l) (typeSubstitute subst r)
typeSubstitute _ AnyT = AnyT

noncaptureTypeSubst :: [Id] -> [RType] -> RType -> RType
noncaptureTypeSubst tVars tArgs t =
  let tFresh = typeSubstitute (Map.fromList $ zip tVars (map vartAll distinctTypeVars)) t
  in typeSubstitute (Map.fromList $ zip distinctTypeVars tArgs) tFresh

schemaSubstitute :: TypeSubstitution -> RSchema -> RSchema
schemaSubstitute tass (Monotype t) = Monotype $ typeSubstitute tass t
schemaSubstitute tass (ForallT a sch) = ForallT a $ schemaSubstitute (Map.delete a tass) sch
schemaSubstitute tass (ForallP sig sch) = ForallP sig $ schemaSubstitute tass sch

typeSubstitutePred :: Substitution -> RType -> RType
typeSubstitutePred pSubst t = let tsp = typeSubstitutePred pSubst
  in case t of
    ScalarT (DatatypeT name tArgs pArgs) fml -> ScalarT (DatatypeT name (map tsp tArgs) (map (substitutePredicate pSubst) pArgs)) (substitutePredicate pSubst fml)
    ScalarT baseT fml -> ScalarT baseT (substitutePredicate pSubst fml)
    FunctionT x tArg tRes -> FunctionT x (tsp tArg) (tsp tRes)
    LetT x tDef tBody -> LetT x (tsp tDef) (tsp tBody)
    AndT l r -> AndT (tsp l) (tsp r)
    AnyT -> AnyT

-- | 'typeVarsOf' @t@ : all type variables in @t@
typeVarsOf :: TypeSkeleton r -> Set Id
typeVarsOf t@(ScalarT baseT r) = case baseT of
  TypeVarT _ name -> Set.singleton name
  DatatypeT _ tArgs _ -> Set.unions (map typeVarsOf tArgs)
  _ -> Set.empty
typeVarsOf (FunctionT _ tArg tRes) = typeVarsOf tArg `Set.union` typeVarsOf tRes
typeVarsOf (LetT _ tDef tBody) = typeVarsOf tDef `Set.union` typeVarsOf tBody
typeVarsOf (AndT l r) = typeVarsOf l `Set.union` typeVarsOf r
typeVarsOf _ = Set.empty

testType :: TypeSkeleton Formula
testType = AndT t2 t3
  where
    myint = ScalarT IntT ftrue
    mybool = ScalarT BoolT ftrue
    t1 = FunctionT "x" myint myint
    t2 = FunctionT "x"
      (ScalarT (DatatypeT "Pair" [myint, mybool, mybool] []) ftrue)
      (ScalarT (DatatypeT "Pair" [myint, mybool, mybool] []) ftrue)
    t3 = FunctionT "x"
      (ScalarT (DatatypeT "Pair" [mybool, myint, mybool] []) ftrue)
      (ScalarT (DatatypeT "Pair" [mybool, myint, mybool] []) ftrue)

-- | What is the essential structure of the type?
-- Remove the refinements, preserve the arrow structure,
-- and infer the least common generalization.
shape :: RType -> SType
shape (AndT l r) = antiUnify (removeRefinement l) (removeRefinement r)
shape t = removeRefinement t

-- | Remove the refinement, but keep the same constructor structure.
removeRefinement :: RType -> SType
removeRefinement (ScalarT (DatatypeT name tArgs pArgs) _) = ScalarT (DatatypeT name (map removeRefinement tArgs) (replicate (length pArgs) ())) ()
removeRefinement (ScalarT IntT _) = ScalarT IntT ()
removeRefinement (ScalarT BoolT _) = ScalarT BoolT ()
removeRefinement (ScalarT (TypeVarT _ a) _) = ScalarT (TypeVarT Map.empty a) ()
removeRefinement (FunctionT x tArg tFun) = FunctionT x (removeRefinement tArg) (removeRefinement tFun)
removeRefinement (LetT _ _ t) = removeRefinement t
removeRefinement (AndT l r) = AndT (removeRefinement l) (removeRefinement r)
removeRefinement AnyT = AnyT

-- antiUnify :: Ord a => TypeSkeleton a -> TypeSkeleton a -> TypeSkeleton a
antiUnify t1 t2 = antiUnify' () t1 t2 Map.empty & fst
-- Implementation taken from James et al. 2020
antiUnify' def (AndT ll lr) r st = uncurry (antiUnify' def r) (antiUnify' def ll lr st)
antiUnify' def l (AndT rl rr) st = uncurry (antiUnify' def l) (antiUnify' def rl rr st)
antiUnify' def (FunctionT x lArg lRet) (FunctionT y rArg rRet) st =
    let (tArg, st1) = antiUnify' def lArg rArg st
        (tRet, st2) = antiUnify' def lRet rRet st1
     in (FunctionT x tArg tRet, st2)
antiUnify' def (ScalarT (DatatypeT n lArgs _) _) (ScalarT (DatatypeT m rArgs _) _) st
    | n == m && length lArgs == length rArgs =
        let (tArgs, stFinal) =
                foldr
                    (\(lTCon, rTCon) (resCon, st') -> first (:resCon) (antiUnify' def lTCon rTCon st'))
                    ([], st)
                    (zip lArgs rArgs)
         in (ScalarT (DatatypeT n tArgs (replicate (length lArgs) def)) def, stFinal)
antiUnify' def l r st
    | l == r = (l, st)
    | (l, r) `Map.member` st = (ScalarT (TypeVarT Map.empty (st Map.! (l, r))) def, st)
    | otherwise =
        let newKeyname = mkFreshIdSafe (Map.elems st) 0
            st' = Map.insert (l, r) newKeyname st
         in (ScalarT (TypeVarT Map.empty newKeyname) def, st')
  where
    mkFreshIdSafe ks idx =
        if ("T" ++ show idx) `elem` ks
            then mkFreshIdSafe ks (idx + 1)
            else "T" ++ show idx


-- | Conjoin refinement to a type
addRefinement :: TypeSkeleton Formula -> Formula -> TypeSkeleton Formula
addRefinement (ScalarT base fml) fml' = if isVarRefinement fml'
  then ScalarT base fml' -- the type of a polymorphic variable does not require any other refinements
  else ScalarT base (fml `andClean` fml')
addRefinement (LetT x tDef tBody) fml = LetT x tDef (addRefinement tBody fml)
addRefinement t (BoolLit True) = t
addRefinement AnyT _ = AnyT
addRefinement t _ = error $ "addRefinement: applied to function type: " ++ show t

-- | Conjoin refinement to the return type
addRefinementToLast t@(ScalarT _ _) fml = addRefinement t fml
addRefinementToLast (FunctionT x tArg tRes) fml = FunctionT x tArg (addRefinementToLast tRes fml)
addRefinementToLast (LetT x tDef tBody) fml = LetT x tDef (addRefinementToLast tBody fml)

-- | Conjoin refinement to the return type inside a schema
addRefinementToLastSch :: SchemaSkeleton Formula -> Formula -> SchemaSkeleton Formula
addRefinementToLastSch (Monotype t) fml = Monotype $ addRefinementToLast t fml
addRefinementToLastSch (ForallT a sch) fml = ForallT a $ addRefinementToLastSch sch fml
addRefinementToLastSch (ForallP sig sch) fml = ForallP sig $ addRefinementToLastSch sch fml

-- | Apply variable substitution in all formulas inside a type
substituteInType :: (Id -> Bool) -> Substitution -> RType -> RType
substituteInType isBound subst (ScalarT baseT fml) = ScalarT (substituteBase baseT) (substitute subst fml)
  where
    substituteBase (TypeVarT oldSubst a) = TypeVarT oldSubst a
      -- Looks like pending substitutions on types are not actually needed, since renamed variables are always out of scope
       -- if isBound a
          -- then TypeVarT oldSubst a
          -- else TypeVarT (oldSubst `composeSubstitutions` subst) a
    substituteBase (DatatypeT name tArgs pArgs) = DatatypeT name (map (substituteInType isBound subst) tArgs) (map (substitute subst) pArgs)
    substituteBase baseT = baseT
substituteInType isBound subst (FunctionT x tArg tRes) =
  if Map.member x subst
    then error $ unwords ["Attempt to substitute variable", x, "bound in a function type"]
    else FunctionT x (substituteInType isBound subst tArg) (substituteInType isBound subst tRes)
substituteInType isBound subst (LetT x tDef tBody) =
  if Map.member x subst
    then error $ unwords ["Attempt to substitute variable", x, "bound in a contextual type"]
    else LetT x (substituteInType isBound subst tDef) (substituteInType isBound subst tBody)
substituteInType isBound subst (AndT l r) = AndT (substituteInType isBound subst l) (substituteInType isBound subst r)
substituteInType isBound subst AnyT = AnyT

-- | 'renameVar' @old new t typ@: rename all occurrences of @old@ in @typ@ into @new@ of type @t@
renameVar :: (Id -> Bool) -> Id -> Id -> RType -> RType -> RType
renameVar isBound old new (ScalarT b _)     t = substituteInType isBound (Map.singleton old (Var (toSort b) new)) t
renameVar isBound old new (LetT _ _ tBody)  t = renameVar isBound old new tBody t
renameVar isBound old new (AndT _ _) t = $(todo "unhandled renameVar")
renameVar _ _ _ _                           t = t -- function arguments cannot occur in types (and AnyT is assumed to be function)

-- | Intersection of two types (assuming the types were already checked for consistency)
intersection _ t AnyT = t
intersection _ AnyT t = t
intersection isBound (ScalarT baseT fml) (ScalarT baseT' fml') = case baseT of
  DatatypeT name tArgs pArgs -> let DatatypeT _ tArgs' pArgs' = baseT' in
                                  ScalarT (DatatypeT name (zipWith (intersection isBound) tArgs tArgs') (zipWith andClean pArgs pArgs')) (fml `andClean` fml')
  _ -> ScalarT baseT (fml `andClean` fml')
intersection isBound (FunctionT x tArg tRes) (FunctionT y tArg' tRes') = FunctionT x tArg (intersection isBound tRes (renameVar isBound y x tArg tRes'))

-- | Instantiate unknowns in a type
typeApplySolution :: Solution -> RType -> RType
typeApplySolution sol (ScalarT (DatatypeT name tArgs pArgs) fml) = ScalarT (DatatypeT name (map (typeApplySolution sol) tArgs) (map (applySolution sol) pArgs)) (applySolution sol fml)
typeApplySolution sol (ScalarT base fml) = ScalarT base (applySolution sol fml)
typeApplySolution sol (FunctionT x tArg tRes) = FunctionT x (typeApplySolution sol tArg) (typeApplySolution sol tRes)
typeApplySolution sol (LetT x tDef tBody) = LetT x (typeApplySolution sol tDef) (typeApplySolution sol tBody)
typeApplySolution _ AndT{} = $(todo "typeApplySolution incomplete")
typeApplySolution _ AnyT = AnyT

typeFromSchema :: RSchema -> RType
typeFromSchema (Monotype t) = t
typeFromSchema (ForallT _ t) = typeFromSchema t
typeFromSchema (ForallP _ t) = typeFromSchema t

allRefinementsOf :: RSchema -> [Formula]
allRefinementsOf sch = allRefinementsOf' $ typeFromSchema sch

allRefinementsOf' (ScalarT _ ref) = [ref]
allRefinementsOf' (FunctionT _ argT resT) = allRefinementsOf' argT ++ allRefinementsOf' resT
allRefinementsOf' _ = error "allRefinementsOf called on contextual or any type"

simplifyType :: RType -> RType
simplifyType t@(AndT l _)
  | allSame (intersectionToList t) = l
  -- | (ScalarT repB _) <- head (intersectionToList t)
  -- , allSame (map baseTypeOf)
simplifyType t@(UnionT l _)
  | allSame (unionToList t) = l
  -- We can only truely lift scalar unions to refinements
  | (ScalarT repB _) <- head (unionToList t)
  , allSame (map baseTypeOf (unionToList t)) = let
      fmls = concatMap allRefinementsOf' $ unionToList t
    in ScalarT repB (foldr1 (|||) fmls)
  | otherwise = let
      ts = unionToList t
      baseTys = groupBy (on (==) baseTypeOf) ts
      fps = map (simplifyType . (foldr1 UnionT)) baseTys
    in foldr1 UnionT fps
simplifyType t = t

enforceWorldNames :: [RType] -> [RType]
enforceWorldNames [] = []
enforceWorldNames (t:ts) = t : map (matchNames t) ts

matchNames :: RType -> RType -> RType
matchNames = matchNames' Map.empty
  where
    matchNames' subst (FunctionT x argTemplate resTemplate) (FunctionT y arg res) =
      let arg' = matchNames' subst argTemplate arg in
      case arg of
        ScalarT base _ ->
          FunctionT x (substituteInType (const False) subst arg') (matchNames' (Map.insert y (Var (toSort base) x) subst) resTemplate res)
        _ -> FunctionT x (substituteInType (const False) subst arg') (matchNames' subst resTemplate res)
    matchNames' subst _ t = substituteInType (const False) subst t

-- Set strings: used for "fake" set type for typechecking measures
emptySetCtor = "Emptyset"
singletonCtor = "Singleton"
insertSetCtor = "Insert"
setTypeName = "DSet"
setTypeVar = "setTypeVar"
setConstructors = [emptySetCtor, singletonCtor, insertSetCtor]