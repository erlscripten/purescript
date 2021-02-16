-- |
-- This module implements the desugaring pass which replaces top-level binders with
-- case expressions.
--
module Language.PureScript.Sugar.CaseDeclarations
  ( desugarCases
  , desugarCasesModule
  , desugarCaseGuards
  ) where

import Prelude.Compat
import Protolude (ordNub)

import Data.List (groupBy, foldl1')
import Data.Maybe (catMaybes, mapMaybe)

import Control.Monad ((<=<), forM, replicateM, join, unless)
import Control.Monad.Error.Class (MonadError(..))
import Control.Monad.Supply.Class

import Language.PureScript.AST
import Language.PureScript.Crash
import Language.PureScript.Environment
import Language.PureScript.Errors
import Language.PureScript.Names
import Language.PureScript.TypeChecker.Monad (guardWith)
import qualified Language.PureScript.Constants as C

-- |
-- Replace all top-level binders in a module with case expressions.
--
desugarCasesModule
  :: (MonadSupply m, MonadError MultipleErrors m)
  => Module
  -> m Module
desugarCasesModule (Module ss coms name ds exps) =
  rethrow (addHint (ErrorInModule name)) $
    Module ss coms name
      <$> (desugarCases <=< desugarAbs <=< validateCases $ ds)
      <*> pure exps

desugarCaseGuards
  :: forall m. (MonadSupply m, MonadError MultipleErrors m)
  => [Declaration]
  -> m [Declaration]
desugarCaseGuards declarations = parU declarations go
  where
    go d =
      let (f, _, _) = everywhereOnValuesM return (desugarGuardedExprs (declSourceSpan d)) return
      in f d

-- |
-- Desugar case with pattern guards and pattern clauses to a
-- series of nested case expressions.
--
desugarGuardedExprs
  :: forall m. (MonadSupply m)
  => SourceSpan
  -> Expr
  -> m Expr
desugarGuardedExprs ss (Case scrut alternatives)
  | any (not . isTrivialExpr) scrut = do
    -- in case the scrutinee is non trivial (e.g. not a Var or Literal)
    -- we may evaluate the scrutinee more than once when a guard occurrs.
    -- We bind the scrutinee to Vars here to mitigate this case.
    (scrut', scrut_decls) <- unzip <$> forM scrut (\e -> do
      scrut_id <- freshIdent'
      pure ( Var ss (Qualified Nothing scrut_id)
           , ValueDecl (ss, []) scrut_id Private [] [MkUnguarded e]
           )
      )
    Let FromLet scrut_decls <$> desugarGuardedExprs ss (Case scrut' alternatives)
  where
    isTrivialExpr (Var _ _) = True
    isTrivialExpr (Literal _ _) = True
    isTrivialExpr (Accessor _ e) = isTrivialExpr e
    isTrivialExpr (Parens e) = isTrivialExpr e
    isTrivialExpr (PositionedValue _ _ e) = isTrivialExpr e
    isTrivialExpr (TypedValue _ e _) = isTrivialExpr e
    isTrivialExpr _ = False

desugarGuardedExprs ss (Case scrut alternatives) =
  let
    desugarAlternatives :: [CaseAlternative]
                        -> m [CaseAlternative]
    desugarAlternatives = mapM desugarAlternative

    desugarAlternative (CaseAlternative ab ge) = do
      dge <- forM ge $ \(GuardedExpr g e) -> GuardedExpr (desugarGuard g) <$> desugarGuardedExprs ss e
      return $ CaseAlternative ab dge

    -- -- Special case: CoreFn understands single condition guards on
    -- -- binders right hand side.
    -- desugarAlternatives (CaseAlternative ab ge : as)
    --   | not (null cond_guards) =
    --       (CaseAlternative ab cond_guards :)
    --         <$> desugarGuardedAlternative ab rest as
    --   | otherwise = desugarGuardedAlternative ab ge as
    --   where
    --     (cond_guards, rest) = span isSingleCondGuard ge

    --     isSingleCondGuard (GuardedExpr [ConditionGuard _] _) = True
    --     isSingleCondGuard _ = False

    -- desugarGuardedAlternative :: [Binder]
    --                           -> [GuardedExpr]
    --                           -> [CaseAlternative]
    --                           -> m [CaseAlternative]
    -- desugarGuardedAlternative _vb [] rem_alts =
    --   desugarAlternatives rem_alts

    -- desugarGuardedAlternative vb (GuardedExpr gs e : ge) rem_alts = do
    --   rhs <- desugarAltOutOfLine vb ge rem_alts $ \alt_fail ->
    --     Case scrut
    --     (CaseAlternative vb (desugarGuard gs)
    --       : alt_fail' (length scrut))


    desugarGuard :: [Guard] -> [Guard]
    desugarGuard (ConditionGuard c1 : ConditionGuard c2 : gs) =
      desugarGuard (ConditionGuard (
                       App (App (App (Var ss (Qualified (Just (ModuleName "Data.HeytingAlgebra")) (Ident C.conj)))
                                  (Var ss (Qualified (Just (ModuleName "Data.HeytingAlgebra")) (Ident C.heytingAlgebraBoolean))))
                                 c1)
                             c2)
                     : gs)
    desugarGuard [] = []
    desugarGuard (h:t) = h:desugarGuard t

    -- we generate a let-binding for the remaining guards
    -- and alternatives. A CaseAlternative is passed (or in
    -- fact the original case is partial non is passed) to
    -- mk_body which branches to the generated let-binding.
    desugarAltOutOfLine :: [Binder]
                        -> [GuardedExpr]
                        -> [CaseAlternative]
                        -> ((Int -> [CaseAlternative]) -> Expr)
                        -> m Expr
    desugarAltOutOfLine alt_binder rem_guarded rem_alts mk_body
      | Just rem_case <- mkCaseOfRemainingGuardsAndAlts = do
        desugared <- desugarGuardedExprs ss rem_case
        let
          alt_fail :: Int -> [CaseAlternative]
          alt_fail n = [CaseAlternative (replicate n NullBinder) [MkUnguarded desugared]]

        pure $ mk_body alt_fail
        -- pure $ Let FromLet [
        --   ValueDecl (ss, []) rem_case_id Private []
        --     [MkUnguarded (Abs (VarBinder ss unused_binder) desugared)]
        --   ] (mk_body alt_fail)

      | otherwise
      = pure $ mk_body (const [])
      where
        mkCaseOfRemainingGuardsAndAlts
          | not (null rem_guarded)
          = Just $ Case scrut (CaseAlternative alt_binder rem_guarded : rem_alts)
          | not (null rem_alts)
          = Just $ Case scrut rem_alts
          | otherwise
          = Nothing

    scrut_nullbinder :: [Binder]
    scrut_nullbinder = replicate (length scrut) NullBinder

    -- case expressions with a single alternative which have
    -- a NullBinder occur frequently after desugaring
    -- complex guards. This function removes these superflous
    -- cases.
    optimize :: Expr -> Expr
    optimize (Case _ [CaseAlternative vb [MkUnguarded v]])
      | all isNullBinder vb = v
      where
        isNullBinder NullBinder = True
        isNullBinder (PositionedBinder _ _ b) = isNullBinder b
        isNullBinder (TypedBinder _ b) = isNullBinder b
        isNullBinder _ = False
    optimize e = e
  in do
    alts' <- desugarAlternatives alternatives
    return $ optimize (Case scrut alts')

desugarGuardedExprs ss (TypedValue infered e ty) =
  TypedValue infered <$> desugarGuardedExprs ss e <*> pure ty

desugarGuardedExprs _ (PositionedValue ss comms e) =
  PositionedValue ss comms <$> desugarGuardedExprs ss e

desugarGuardedExprs _ v = pure v

-- |
-- Validates that case head and binder lengths match.
--
validateCases :: forall m. (MonadSupply m, MonadError MultipleErrors m) => [Declaration] -> m [Declaration]
validateCases = flip parU f
  where
  (f, _, _) = everywhereOnValuesM return validate return

  validate :: Expr -> m Expr
  validate c@(Case vs alts) = do
    let l = length vs
        alts' = filter ((l /=) . length . caseAlternativeBinders) alts
    unless (null alts') $
      throwError . MultipleErrors $ fmap (altError l) (caseAlternativeBinders <$> alts')
    return c
  validate other = return other

  altError :: Int -> [Binder] -> ErrorMessage
  altError l bs = withPosition pos $ ErrorMessage [] $ CaseBinderLengthDiffers l bs
    where
    pos = foldl1' widenSpan (mapMaybe positionedBinder bs)

    widenSpan (SourceSpan n start end) (SourceSpan _ start' end') =
      SourceSpan n (min start start') (max end end')

    positionedBinder (PositionedBinder p _ _) = Just p
    positionedBinder _ = Nothing

desugarAbs :: forall m. (MonadSupply m, MonadError MultipleErrors m) => [Declaration] -> m [Declaration]
desugarAbs = flip parU f
  where
  (f, _, _) = everywhereOnValuesM return replace return

  replace :: Expr -> m Expr
  replace (Abs (stripPositioned -> (VarBinder ss i)) val) =
    pure (Abs (VarBinder ss i) val)
  replace (Abs binder val) = do
    ident <- freshIdent'
    return $ Abs (VarBinder nullSourceSpan ident) $ Case [Var nullSourceSpan (Qualified Nothing ident)] [CaseAlternative [binder] [MkUnguarded val]]
  replace other = return other

stripPositioned :: Binder -> Binder
stripPositioned (PositionedBinder _ _ binder) = stripPositioned binder
stripPositioned binder = binder

-- |
-- Replace all top-level binders with case expressions.
--
desugarCases :: forall m. (MonadSupply m, MonadError MultipleErrors m) => [Declaration] -> m [Declaration]
desugarCases = desugarRest <=< fmap join . flip parU toDecls . groupBy inSameGroup
  where
    desugarRest :: [Declaration] -> m [Declaration]
    desugarRest (TypeInstanceDeclaration sa cd idx name constraints className tys ds : rest) =
      (:) <$> (TypeInstanceDeclaration sa cd idx name constraints className tys <$> traverseTypeInstanceBody desugarCases ds) <*> desugarRest rest
    desugarRest (ValueDecl sa name nameKind bs result : rest) =
      let (_, f, _) = everywhereOnValuesTopDownM return go return
          f' = mapM (\(GuardedExpr gs e) -> GuardedExpr gs <$> f e)
      in (:) <$> (ValueDecl sa name nameKind bs <$> f' result) <*> desugarRest rest
      where
      go (Let w ds val') = Let w <$> desugarCases ds <*> pure val'
      go other = return other
    desugarRest (d : ds) = (:) d <$> desugarRest ds
    desugarRest [] = pure []

inSameGroup :: Declaration -> Declaration -> Bool
inSameGroup (ValueDeclaration vd1) (ValueDeclaration vd2) = valdeclIdent vd1 == valdeclIdent vd2
inSameGroup _ _ = False

toDecls :: forall m. (MonadSupply m, MonadError MultipleErrors m) => [Declaration] -> m [Declaration]
toDecls [ValueDecl sa@(ss, _) ident nameKind bs [MkUnguarded val]] | all isIrrefutable bs = do
  args <- mapM fromVarBinder bs
  let body = foldr (Abs . VarBinder ss) val args
  guardWith (errorMessage' ss (OverlappingArgNames (Just ident))) $ length (ordNub args) == length args
  return [ValueDecl sa ident nameKind [] [MkUnguarded body]]
  where
  fromVarBinder :: Binder -> m Ident
  fromVarBinder NullBinder = freshIdent'
  fromVarBinder (VarBinder _ name) = return name
  fromVarBinder (PositionedBinder _ _ b) = fromVarBinder b
  fromVarBinder (TypedBinder _ b) = fromVarBinder b
  fromVarBinder _ = internalError "fromVarBinder: Invalid argument"
toDecls ds@(ValueDecl (ss, _) ident _ bs (result : _) : _) = do
  let tuples = map toTuple ds

      isGuarded (MkUnguarded _) = False
      isGuarded _               = True

  unless (all ((== length bs) . length . fst) tuples) .
    throwError . errorMessage' ss $ ArgListLengthsDiffer ident
  unless (not (null bs) || isGuarded result) .
    throwError . errorMessage' ss $ DuplicateValueDeclaration ident
  caseDecl <- makeCaseDeclaration ss ident tuples
  return [caseDecl]
toDecls ds = return ds

toTuple :: Declaration -> ([Binder], [GuardedExpr])
toTuple (ValueDecl _ _ _ bs result) = (bs, result)
toTuple _ = internalError "Not a value declaration"

makeCaseDeclaration :: forall m. (MonadSupply m) => SourceSpan -> Ident -> [([Binder], [GuardedExpr])] -> m Declaration
makeCaseDeclaration ss ident alternatives = do
  let namedArgs = map findName . fst <$> alternatives
      argNames = foldl1 resolveNames namedArgs
  args <- if allUnique (catMaybes argNames)
            then mapM argName argNames
            else replicateM (length argNames) freshIdent'
  let vars = map (Var ss . Qualified Nothing) args
      binders = [ CaseAlternative bs result | (bs, result) <- alternatives ]
  let value = foldr (Abs . VarBinder ss) (Case vars binders) args

  return $ ValueDecl (ss, []) ident Public [] [MkUnguarded value]
  where
  -- We will construct a table of potential names.
  -- VarBinders will become Just _ which is a potential name.
  -- Everything else becomes Nothing, which indicates that we
  -- have to generate a name.
  findName :: Binder -> Maybe Ident
  findName (VarBinder _ name) = Just name
  findName (PositionedBinder _ _ binder) = findName binder
  findName _ = Nothing

  -- We still have to make sure the generated names are unique, or else
  -- we will end up constructing an invalid function.
  allUnique :: (Ord a) => [a] -> Bool
  allUnique xs = length xs == length (ordNub xs)

  argName :: Maybe Ident -> m Ident
  argName (Just name) = return name
  argName _ = freshIdent'

  -- Combine two lists of potential names from two case alternatives
  -- by zipping correspoding columns.
  resolveNames :: [Maybe Ident] -> [Maybe Ident] -> [Maybe Ident]
  resolveNames = zipWith resolveName

  -- Resolve a pair of names. VarBinder beats NullBinder, and everything
  -- else results in Nothing.
  resolveName :: Maybe Ident -> Maybe Ident -> Maybe Ident
  resolveName (Just a) (Just b)
    | a == b = Just a
    | otherwise = Nothing
  resolveName _ _ = Nothing
