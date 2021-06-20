{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, TemplateHaskell #-}

-- | Interface to Z3
module Synquid.Z3 (Z3State, evalZ3State) where

import Synquid.Logic
import Synquid.Type
import Synquid.Types.Logic
import Synquid.Types.Program
import Synquid.Types.Type
import Synquid.Types.Rest
import Synquid.Program
import Synquid.SolverMonad
import Synquid.Util ( bothM, ifM, partitionM, Id )
import Synquid.Pretty (brackets,  text, Pretty(pretty), ($+$), (<+>), (</>), commaSep )
import Z3.Monad hiding (Z3Env, newEnv, Sort)
import qualified Z3.Base as Z3

import Data.Maybe
import Data.List
import Data.List.Extra (replace)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Bimap as Bimap
import Data.Bimap (Bimap)

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Applicative
import Control.Lens hiding (both)

import Debug.Trace
import Development.Placeholders

-- | Z3 state while building constraints
data Z3Data = Z3Data {
  _mainEnv :: Z3Env,                          -- ^ Z3 environment for the main solver
  _sorts :: Map Sort Z3.Sort,                 -- ^ Mapping from Synquid sorts to Z3 sorts
  _vars :: Map Id AST,                        -- ^ AST nodes for scalar variables
  _functions :: Map Id FuncDecl,              -- ^ Function declarations for measures, predicates, and constructors
  _storedDatatypes :: Map Id Z3.Sort,         -- ^ Datatypes mapped directly to Z3 datatypes (monomorphic only)
  _controlLiterals :: Bimap Formula AST,      -- ^ Control literals for computing UNSAT cores
  _auxEnv :: Z3Env,                           -- ^ Z3 environment for the auxiliary solver
  _boolSortAux :: Maybe Z3.Sort,              -- ^ Boolean sort in the auxiliary solver
  _controlLiteralsAux :: Bimap Formula AST,    -- ^ Control literals for computing UNSAT cores in the auxiliary solver
  _synquidSymbols :: Map Id RSchema,
  _synquidDatatypes :: Map Id DatatypeDef
}

data Z3Env = Z3Env {
  envSolver  :: Z3.Solver,
  envContext :: Z3.Context
}

makeLenses ''Z3Data

initZ3Data env env' = Z3Data {
  _mainEnv = env,
  _sorts = Map.empty,
  _vars = Map.empty,
  _functions = Map.empty,
  _storedDatatypes = Map.empty,
  _controlLiterals = Bimap.empty,
  _auxEnv = env',
  _boolSortAux = Nothing,
  _controlLiteralsAux = Bimap.empty,
  _synquidSymbols = Map.empty,
  _synquidDatatypes = Map.empty
}

type Z3State = StateT Z3Data IO

instance MonadSMT Z3State where
  initSolver env = do
    -- Disable MBQI:
    setASTPrintMode Z3_PRINT_SMTLIB_FULL
    params <- mkParams
    symb <- mkStringSymbol "mbqi"
    paramsSetBool params symb False
    pstring <- paramsToString params
    debug 2 (text "[MonadSMT]: init: " <+> (text $ pstring)) (return ())
    solverSetParams params
    std <- uses storedDatatypes id
    synquidSymbols .= allSymbols env
    synquidDatatypes .= (env ^. datatypes)

    -- debug 2 (text "[MonadSMT]: init: symbols: " <+> (pretty $ Map.toList $ allSymbols env)) (return ())
    -- debug 2 (text "[MonadSMT]: init: datatypes: " <+> (pretty $ show $ env ^. datatypes)) (return ())
    -- debug 2 (text "[MonadSMT]: init: stored datatypes:" <+> (pretty $ show $ std)) (return ())
    convertDatatypes (allSymbols env) (Map.toList $ env ^. datatypes)

    -- debug 2 (text "[MonadSMT]: init: Created." ) (return ())
    boolAux <- withAuxSolver mkBoolSort
    boolSortAux .= Just boolAux

  isSat fml = do
      res <- local $ (fmlToAST >=> assert') fml >> check

      case res of
        Unsat -> debug 2 (text "SMT CHECK" <+> pretty fml <+> text "UNSAT") $ return False
        Sat -> do
          debug 2 (text "SMT CHECK" <+> pretty fml <+> text "SAT") $ return True
          -- model <- solverGetModel
          -- satModelStr <- modelToString model
          -- debug 2 (brackets (text "isSat") <> text ": SAT model:" </> text satModelStr) $
          -- return True
        -- _ -> error $ unwords ["isValid: Z3 returned Unknown for", show fml]
        _ -> debug 2 (text "SMT CHECK" <+> pretty fml <+> text "UNKNOWN treating as SAT") $ return True

  allUnsatCores = getAllMUSs

assert' ast = do
    _true <- mkTrue
    str <- benchmarkToSMTLibString "[partial-refinement]" "" "unknown" ""
                  [ast]
                  _true
    s <- astToString ast
    -- debug 2 (text "[MonadSMT]: isSat:" </> text s) $
    -- debug 3 (text "[MonadSMT]: Z3 query:" </> text str) $
    assert ast

convertDatatypes :: Map Id RSchema -> [(Id, DatatypeDef)] -> Z3State ()
convertDatatypes _ [] = return ()
-- datatype with no type arguments
convertDatatypes symbols ((dtName, DatatypeDef tyvars _ _ ctors@(_:_) _):rest) = do
  ifM (uses storedDatatypes (Map.member dtName))
    (return ()) -- This datatype has already been processed as a dependency
    (do
      dtSymb <- mkStringSymbol dtName
      z3ctors <- mapM convertCtor ctors
      z3dt <- mkDatatype dtSymb z3ctors
      s <- sortToString z3dt
      sorts %= Map.insert dataSort z3dt
      storedDatatypes %= Map.insert dtName z3dt)
  convertDatatypes symbols rest
  where
    dataSort = DataS dtName []

    convertCtor cName = do
      z3CName <- mkStringSymbol cName
      recognizerName <- mkStringSymbol ("is" ++ cName)
      let args = allArgs $ toMonotype $ symbols Map.! cName
      z3Args <- mapM convertField args
      mkConstructor z3CName recognizerName z3Args

    convertField (Var fSort fName) = do
      z3FName <- mkStringSymbol fName
      z3FSort <- case fSort of
                    DataS dtName' [] ->
                      if dtName' == dtName
                        then return Nothing -- Recursive sort is denoted with Nothing
                        else case lookup dtName' rest of
                              Nothing -> Just <$> toZ3Sort fSort -- Datatype dtName' should have already been processed
                              Just dtDef -> do -- It is an eligible datatype yet to process; process it now instead
                                              convertDatatypes symbols [(dtName', dtDef)]
                                              Just <$> toZ3Sort fSort
                    _ -> Just <$> toZ3Sort fSort
      return (z3FName, z3FSort, 0)

-- Instantiate a datatype, from the type-level to one instantiated with Sorts.
-- This will add new sorts to the environment
-- with names like: List_Bool, Nil_Bool, and Cons_Bool_List_Bool
-- sortsInstances : a list of instances to be assigned to each tyvar in the polymorphic dtname
instantiateDatatype :: Id -> [Sort] -> Z3State Z3.Sort
instantiateDatatype dtName sortsInstances = do
  ctors <- getCtors dtName
  ifM (uses storedDatatypes (Map.member dtInstanceName))
    $(todo "already created instance")
    (do
      mbMonoDt <- uses storedDatatypes (Map.lookup dtName)

      monoDtStr <- maybe (return "<Not in monomorphized sorts>") sortToString mbMonoDt
      dtSymb <- mkStringSymbol dtInstanceName
      z3ctors <- mapM (convertCtor sortsInstances) ctors
      z3dt <- mkDatatype dtSymb z3ctors
      s <- sortToString z3dt
      let dataSort = DataS dtName sortsInstances
      sorts %= Map.insert dataSort z3dt
      sorts %= Map.insert (DataS dtInstanceName []) z3dt
      storedDatatypes %= Map.insert dtInstanceName z3dt
      return z3dt
      )

  where
    -- We may get instances for type variables a b c as [BoolS, IntS, IntS]
    -- But when we need to convert a ctor with type `b -> DT {args}`
    -- We need to be able to instantiate that `b` correctly
    getTyVarMapping :: Z3State (Map Id Sort)
    getTyVarMapping = do
      synquidDts <- use synquidDatatypes
      let dtDef = synquidDts Map.! dtName
      let dtTypeVarNames = dtDef ^. typeParams
      return $ Map.fromList $ zip dtTypeVarNames sortsInstances

    dtInstanceName = instanceName dtName sortsInstances

    getCtors :: Id -> Z3State [Id]
    getCtors dtName = do
      synquidDts <- use synquidDatatypes
      if dtName `Map.member` synquidDts
        then do
          let dtdef = synquidDts Map.! dtName
          return (dtdef ^. constructors)
        else
          return $ error $ unwords ["datatype '", dtName, "' not known to synquid"]



    -- Given the sorts to instantiate with and the uninstantiated name,
    -- produce the instantiated constructor.
    convertCtor :: [Sort] -> Id -> Z3State Constructor
    convertCtor sortInstances cName = do
      let instanceCName = instanceName cName sortInstances
      z3CName <- mkStringSymbol instanceCName
      recognizerName <- mkStringSymbol ("is" ++ instanceCName)
      symbols <- use synquidSymbols
      let args = allArgs $ toMonotype $ symbols Map.! cName
      z3Args <- mapM convertField args
      mkConstructor z3CName recognizerName z3Args

    -- Convert each argument of a ctor into the instantiated version.
    -- Could have an issue with mutual recursion,
    -- or if we hit another polymorphic DT to be instantiated as well
    convertField :: Formula -> Z3State (Symbol, Maybe Z3.Sort, Int)
    convertField (Var fSort fName) = do
      z3FName <- mkStringSymbol fName
      z3FSort <- case fSort of
                    DataS dtName' [] ->  -- Monomorphic
                      if dtName' == dtName
                        then return Nothing -- Recursive sort is denoted with Nothing
                        else error "not possible: an unprocessed monomorphic dt during runtime"
                    DataS dtName' tyvars' -> do -- Polymorphic.
                      -- We need to figure out how to instantiate the type vars from up top.
                      -- this might be prev:Nat a, so we need to align the "a" here
                      -- with the "a" used elsewhere in instantiating this DT
                      -- So they're all consistent.
                      if dtName' == dtName
                        then do -- this argument is the same type as the one we're instantiating
                          return Nothing
                        else do -- this argument needs a different instantiation
                          error $ unwords ["Converting field:", fName, "::", show fSort]
                          $(todo "polymorphic argument to instantiate") -- Just <$> toZ3Sort fSort
                    -- type variable fields need to be instantiated
                    VarS name -> do
                      tyVarMapping <- getTyVarMapping
                      case Map.lookup name tyVarMapping of
                        Nothing -> error $ unwords ["[ConvertField]: Type variable ",
                          name, "not known to this instance. We have",
                          show tyVarMapping]
                        Just synquidSort -> Just <$> toZ3Sort synquidSort
                    unknown@_ -> error $ unwords ["Variable with unknown sort:", show unknown]

      return (z3FName, z3FSort, 0)

-- | An instance name for a parametric datatype: like Either_IntS_BoolS
instanceName :: Id -> [Sort] -> Id
instanceName id sorts = intercalate "_" $ id : map show sorts

-- | Creates a z3-friendly looking sort name
synquidSortToString :: Sort -> Id
synquidSortToString IntS = "IntS"
synquidSortToString BoolS = "BoolS"
synquidSortToString AnyS = "AnyS"
synquidSortToString (SetS el) = "SetS_" ++ synquidSortToString el ++ "__"
synquidSortToString (VarS name) = "VarS_" ++ name
synquidSortToString (DataS name args) = "DataS_" ++ name ++ "_" ++ concatMap synquidSortToString args ++ "__"

-- | Get the literal in the auxiliary solver that corresponds to a given literal in the main solver
litToAux :: AST -> Z3State AST
litToAux lit = do
  fml <- uses controlLiterals (Bimap.!> lit)
  uses controlLiteralsAux (Bimap.! fml)

-- | Get the literal in the main solver that corresponds to a given literal in the auxiliary solver
litFromAux :: AST -> Z3State AST
litFromAux lit = do
  fml <- uses controlLiteralsAux (Bimap.!> lit)
  uses controlLiterals (Bimap.! fml)

-- | Lookup Z3 sort for a Synquid sort.
-- | When we do not have a sort, we create one and store it.
toZ3Sort :: Sort -> Z3State Z3.Sort
toZ3Sort s = do
  resMb <- uses sorts (Map.lookup s)
  res <- case resMb of
    Just z3s -> return z3s
    Nothing -> do
      z3s <- case s of
        BoolS -> mkBoolSort
        IntS -> mkIntSort
        -- VarS name -> mkStringSymbol name >>= mkUninterpretedSort
        VarS name -> mkIntSort
        -- DataS name args -> mkStringSymbol name >>= mkUninterpretedSort
        DataS name [] -> error $ unwords ["toSort on a monomorphic datatype:", name, ". Not sure when this happens."]
        DataS name args -> instantiateDatatype name args
        SetS el -> toZ3Sort el >>= mkSetSort
        AnyS -> mkIntSort
      sorts %= Map.insert s z3s
      return z3s
  resStr <- sortToString res
  return res
instance MonadZ3 Z3State where
  getSolver = gets (envSolver . _mainEnv)
  getContext = gets (envContext . _mainEnv)

-- | Create a new Z3 environment.
newEnv :: Maybe Logic -> Opts -> IO Z3Env
newEnv mbLogic opts =
  Z3.withConfig $ \cfg -> do
    setOpts cfg opts
    ctx <- Z3.mkContext cfg
    solver <- maybe (Z3.mkSolver ctx) (Z3.mkSolverForLogic ctx) mbLogic
    return $ Z3Env solver ctx

-- | Use auxiliary solver to execute a Z3 computation
withAuxSolver :: Z3State a -> Z3State a
withAuxSolver c = do
  m <- use mainEnv
  a <- use auxEnv
  mainEnv .= a
  res <- c
  mainEnv .= m
  return res

evalZ3State :: Z3State a -> IO a
evalZ3State f = do
  -- env <- newEnv (Just QF_AUFLIA) stdOpts
  -- env' <- newEnv (Just QF_AUFLIA) stdOpts
  env <- newEnv Nothing stdOpts
  env' <- newEnv Nothing stdOpts
  evalStateT f $ initZ3Data env env'

-- | Convert a first-order constraint to a Z3 AST.
fmlToAST :: Formula -> Z3State AST
fmlToAST = toAST . simplify
  where
    simplify expr = case expr of
      SetLit el xs -> SetLit el (map simplify xs)
      Unary op e -> Unary op (simplify e)
      Binary op e1 e2 ->
        let e1' = simplify e1
            e2' = simplify e2
        in case sortOf e1' of
             BoolS -> case op of
                        Le -> e1' |=>| e2'
                        Ge -> e2' |=>| e1'
                        Lt -> fnot e1' |&| e2'
                        Gt -> fnot e2' |&| e1'
                        _  -> Binary op e1' e2'
             _ -> Binary op e1' e2'
      Ite e0 e1 e2 -> Ite (simplify e0) (simplify e1) (simplify e2)
      Pred s name args -> Pred s name (map simplify args)
      Cons s name args -> Cons s name (map simplify args)
      All v e -> All v (simplify e)
      _ -> expr

-- | Convert a Synquid refinement term to a Z3 AST
toAST :: Formula -> Z3State AST
toAST expr = case expr of
  BoolLit True  -> mkTrue
  BoolLit False -> mkFalse
  SetLit el xs -> setLiteral el xs
  IntLit i -> mkIntNum i
  Var s name -> var s name
  Unknown _ name -> error $ unwords ["[toAST]: Unknown: encountered a second-order unknown:", name]
  Unary op e -> toAST e >>= unOp op
  Binary op e1 e2 -> join (binOp op <$> toAST e1 <*> toAST e2)
  Ite e0 e1 e2 -> do
    e0' <- toAST e0
    e1' <- toAST e1
    e2' <- toAST e2
    mkIte e0' e1' e2'
  Pred s name args -> do
    let tArgs = map sortOf args
    decl <- function s name tArgs
    mapM toAST args >>= mkApp decl
  Cons s name args -> do
    storeddts <- use storedDatatypes
    storedDtsStr <- mapM (\(dtName,v) -> sortToString v >>= (\sortStr -> return (dtName, sortStr))) $ Map.toList storeddts
    let tArgs = map sortOf args
    fDecl <- constructor s name tArgs
    declStr <- funcDeclToString fDecl
    mapM toAST args >>= mkApp fDecl
  All v e -> accumAll [v] e
  where
    setLiteral el xs = do
      emp <- toZ3Sort el >>= mkEmptySet
      elems <- mapM toAST xs
      foldM mkSetAdd emp elems

    accumAll :: [Formula] -> Formula -> Z3State AST
    accumAll xs (All y e) = accumAll (xs ++ [y]) e
    accumAll xs e = do
      boundVars <- mapM toAST xs
      boundApps <- mapM toApp boundVars
      body <- toAST e

      -- let triggers = case e of
                      -- Binary Implies lhs _ -> [lhs]
                      -- _ -> []
      -- patterns <- mapM (toAST >=> (mkPattern . replicate 1)) triggers
      -- mkForallConst patterns boundApps body
      mkForallConst [] boundApps body

    unOp :: UnOp -> AST -> Z3State AST
    unOp Neg = mkUnaryMinus
    unOp Not = mkNot

    binOp :: BinOp -> AST -> AST -> Z3State AST
    binOp op =
      case op of
        Eq -> mkEq
        Neq -> list2 mkDistinct
        Gt -> mkGt
        Lt -> mkLt
        Le -> mkLe
        Ge -> mkGe
        Times -> list2 mkMul
        Plus -> list2 mkAdd
        Minus -> list2 mkSub
        And   -> list2 mkAnd
        Or    -> list2 mkOr
        Implies -> mkImplies
        Iff -> mkIff
        Union -> list2 mkSetUnion
        Intersect -> list2 mkSetIntersect
        Diff -> mkSetDifference
        Member -> mkSetMember
        Subset -> mkSetSubset
    list2 o x y = o [x, y]

    -- | Lookup or create a variable with name `ident' and sort `s'
    var s ident = do
      let ident' = ident ++ synquidSortToString (asZ3Sort s)
      varMb <- uses vars (Map.lookup ident')

      case varMb of
        Just v -> return v
        Nothing -> do
          symb <- mkStringSymbol ident'
          z3s <- toZ3Sort s
          v <- mkConst symb z3s
          vars %= Map.insert ident' v
          return v

    -- | Lookup or create a function declaration with name `name', return type `resT', and argument types `argTypes'
    function resT name argTypes = do
      let name' = name ++ concatMap (synquidSortToString . asZ3Sort) (resT : argTypes)
      declMb <- uses functions (Map.lookup name')
      case declMb of
        Just d -> return d
        Nothing -> do
          symb <- mkStringSymbol name'
          argSorts <- mapM toZ3Sort argTypes
          resSort <- toZ3Sort resT
          decl <- mkFuncDecl symb argSorts resSort
          declstr <- funcDeclToString decl
          functions %= Map.insert name' decl
          -- return $ traceShow (text "DECLARE" <+> text name <+> pretty argTypes <+> pretty resT) decl
          return decl

    constructor resT cName argTypes =
      case resT of
        DataS dtName [] -> -- monomorphic
          ifM (uses storedDatatypes (Map.member dtName))
            (do
              z3dt <- toZ3Sort resT
              decls <- getDatatypeSortConstructors z3dt
              findDecl cName decls)
            (error (unwords ["constructor", cName, "for datatype", dtName, "not already created in init"])) -- (function resT cName argTypes)
        DataS dtName tyvars -> do
          let dtInstanceName = instanceName dtName tyvars
          let cNameInstance = instanceName cName tyvars
          ifM (uses storedDatatypes (Map.member dtInstanceName))
            (do
              -- This calls again, but with the monomorphized version.
              constructor (DataS dtInstanceName []) cNameInstance argTypes
              )
            (do
              -- We've got to instantiate the type now.
              z3dt <- instantiateDatatype dtName tyvars
              decls <- getDatatypeSortConstructors z3dt
              findDecl cNameInstance decls
            )


    findDecl cName decls = do
      declNames <- mapM (getDeclName >=> getSymbolString) decls
      return $ decls !! fromJust (elemIndex cName declNames)

    -- | Sort as Z3 sees it
    asZ3Sort s = case s of
      VarS _ -> IntS
      -- DataS _ (_:_) -> IntS
      SetS el -> SetS (asZ3Sort el)
      _ -> s


-- | 'getAllMUSs' @assumption mustHave fmls@ : find all minimal unsatisfiable subsets of @fmls@ with @mustHave@, which contain @mustHave@, assuming @assumption@
-- (implements Marco algorithm by Mark H. Liffiton et al.)
getAllMUSs :: Formula -> Formula -> [Formula] -> Z3State [[Formula]]
getAllMUSs assumption mustHave fmls = do
  push
  withAuxSolver push

  let allFmls = mustHave : fmls
  (controlLits, controlLitsAux) <- unzip <$> mapM getControlLits allFmls

  debug 2 (text "getAllMUSs" $+$ text "assumption:" <+> pretty assumption $+$ text "must have:" <+> pretty mustHave $+$ text "fmls:" <+> pretty fmls) $ return ()
  fmlToAST assumption >>= assert
  condAssumptions <- mapM fmlToAST allFmls >>= zipWithM mkImplies controlLits
  mapM_ assert $ condAssumptions
  withAuxSolver $ assert $ head controlLitsAux

  res <- getAllMUSs' controlLitsAux (head controlLits) []
  withAuxSolver $ pop 1
  pop 1
  return res

  where
    getControlLits fml = do
      litMb <- uses controlLiterals (Bimap.lookup fml)
      case litMb of
        Just lit -> do
          litAux <- uses controlLiteralsAux (Bimap.! fml)
          return (lit, litAux)
        Nothing -> do
          bool <- toZ3Sort BoolS
          boolAux <- fromJust <$> use boolSortAux
          name <- ((++ "lit") . show . Bimap.size) <$> use controlLiterals
          lit <- mkStringSymbol name >>= flip mkConst bool
          litAux <- withAuxSolver $ mkStringSymbol name >>= flip mkConst boolAux
          controlLiterals %= Bimap.insert fml lit
          controlLiteralsAux %= Bimap.insert fml litAux
          return (lit, litAux)

getAllMUSs' controlLitsAux mustHave cores = do
  seedMb <- getNextSeed
  case seedMb of
    Nothing -> return cores -- No uncovered subsets left, return the cores accumulated so far
    Just s -> do
      (seed, rest) <- bothM (mapM litFromAux) s
      mapM litToFml seed >>= debugOutput "Seed"
      res <- checkAssumptions seed  -- Check if seed is satisfiable
      case res of
        Unsat -> do                 -- Unsatisfiable: extract MUS
          mus <- getUnsatCore >>= minimize
          blockUp mus
          musStrs <- mapM litToFml mus
          debugOutput "found MUSes:" musStrs

          unsatFmls <- mapM litToFml (delete mustHave mus)
          when (mustHave `elem` mus) (debug 2 (text "Original Synquid MUS") $ return ())
          when (unsatFmls == [ffalse]) (debug 2 (text "MUS solution is vacuous") $ return ())
          debugOutput "MUS" unsatFmls
          getAllMUSs' controlLitsAux mustHave (unsatFmls : cores)
        Sat -> do
          mss <- maximize seed rest  -- Satisfiable: expand to MSS
          blockDown mss
          mapM litToFml mss >>= debugOutput "MSS"
          getAllMUSs' controlLitsAux mustHave cores
        _ -> do
          fmls <- mapM litToFml seed
          error $ unwords $ ["getAllMUSs: Z3 returned Unknown (maybe consider SAT) for"] ++ map show fmls

  where
    -- | Get the formula mapped to a given control literal in the main solver
    litToFml = uses controlLiterals . flip (Bimap.!>)

    -- | Get an unexplored subset of control literals inside the auxiliary solver
    getNextSeed = withAuxSolver $ do
      (res, modelMb) <- getModel
      case res of
        Unsat -> return Nothing -- No unexplored subsets left
        Sat -> Just <$> partitionM (getCtrlLitModel True (fromJust modelMb)) controlLitsAux -- Found unexplored subset: partition @controlLitsAux@ according to the model

    -- | Extract the Boolean value for literal @lit@ from the model @m@ with default @bias@
    getCtrlLitModel bias m lit = do
      resMb <- fromJust <$> eval m lit >>= getBoolValue
      case resMb of
        Nothing -> return bias
        Just b -> return b

    -- | Mark all supersets of @mus@ explored
    blockUp mus = withAuxSolver $ mapM (litToAux >=> mkNot) mus >>= mkOr >>= assert

    -- | Mark all subsets of @mss@ explored
    blockDown mss = withAuxSolver $ do
      mss' <- mapM litToAux mss
      let rest = controlLitsAux \\ mss'
      (if null rest then mkFalse else mkOr rest) >>= assert

    -- | Shrink unsatisfiable set @lits@ to some MUS
    minimize lits = local $ minimize' [] lits
    minimize' checked [] = return checked
    minimize' checked (lit:lits) = do
      res <- checkAssumptions lits
      case res of
        Unsat -> minimize' checked lits -- lit can be omitted
        _ -> assert lit >> minimize' (lit:checked) lits -- lit required for UNSAT: leave it in the minimal core

    -- | Grow satisfiable set @checked@ with literals from @rest@ to some MSS
    maximize checked rest = local $ mapM_ assert checked >> maximize' checked rest
    maximize' checked [] = return checked -- checked includes all literals and thus must be maximal
    maximize' checked rest = do
      mkOr rest >>= assert
      (res, modelMb) <- getModel
      case res of
        Unsat -> return checked -- cannot add any literals, checked is maximal
        _ -> do -- found some literals to add; fix them and continue
          (setRest, unsetRest) <- partitionM (getCtrlLitModel True (fromJust modelMb)) rest
          mapM_ assert setRest
          maximize' (checked ++ setRest) unsetRest

    debugOutput label fmls = debug 2 (text label <+> pretty fmls) $ return ()

-- | 'debugOutLevel' : Level above which debug output is ignored
debugOutLevel = 0

-- | 'debug' @level msg@ : output @msg@ at level @level@
debug level msg = if level <= debugOutLevel then traceShow msg else id
