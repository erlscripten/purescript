-- |
-- This module implements the desugaring pass which creates binding groups from sets of
-- mutually-recursive value declarations and mutually-recursive type declarations.
--
module Language.PureScript.Sugar.BindingGroups
  ( createBindingGroups
  , createBindingGroupsModule
  , collapseBindingGroups
  , collapseBindingGroupsModule
  ) where

import Prelude.Compat
import Protolude (ordNub)

import Control.Monad ((<=<))
import Control.Monad.Error.Class (MonadError(..))

import Data.Array (bounds, (!))
import Data.Graph
import Data.List (intersect)
import Data.Foldable (find)
import Data.Maybe (fromJust, isJust, mapMaybe)
import qualified Data.List.NonEmpty as NEL
import qualified Data.Set as S

import Language.PureScript.AST
import Language.PureScript.Crash
import Language.PureScript.Environment
import Language.PureScript.Errors
import Language.PureScript.Names
import Language.PureScript.Types

-- |
-- Replace all sets of mutually-recursive declarations in a module with binding groups
--
createBindingGroupsModule
  :: (MonadError MultipleErrors m)
  => Module
  -> m Module
createBindingGroupsModule (Module ss coms name ds exps) =
  Module ss coms name <$> createBindingGroups name ds <*> pure exps

-- |
-- Collapse all binding groups in a module to individual declarations
--
collapseBindingGroupsModule :: [Module] -> [Module]
collapseBindingGroupsModule =
  fmap $ \(Module ss coms name ds exps) ->
    Module ss coms name (collapseBindingGroups ds) exps

createBindingGroups
  :: forall m
   . (MonadError MultipleErrors m)
  => ModuleName
  -> [Declaration]
  -> m [Declaration]
createBindingGroups moduleName = mapM f <=< handleDecls

  where
  (f, _, _) = everywhereOnValuesTopDownM return handleExprs return

  handleExprs :: Expr -> m Expr
  handleExprs (Let w ds val) = (\ds' -> Let w ds' val) <$> handleDecls ds
  handleExprs other = return other

  -- |
  -- Replace all sets of mutually-recursive declarations with binding groups
  --
  handleDecls :: [Declaration] -> m [Declaration]
  handleDecls ds = do
    let values = mapMaybe (fmap (fmap extractGuardedExpr) . getValueDeclaration) ds
        dataDecls = filter isDataDecl ds
        allProperNames = fmap declTypeName dataDecls
        dataVerts = fmap (\d -> (d, declTypeName d, usedTypeNames moduleName d `intersect` allProperNames)) dataDecls
    dataBindingGroupDecls <- parU (stronglyConnComp dataVerts) toDataBindingGroup
    let allIdents = fmap valdeclIdent values
        valueVerts = fmap (\d -> (d, valdeclIdent d, usedIdents moduleName d `intersect` allIdents)) values
    bindingGroupDecls <- parU (stronglyConnComp valueVerts) (toBindingGroup moduleName)
    return $ filter isImportDecl ds ++
             filter isExternKindDecl ds ++
             filter isExternDataDecl ds ++
             dataBindingGroupDecls ++
             filter isTypeClassDeclaration ds ++
             filter isTypeClassInstanceDeclaration ds ++
             filter isFixityDecl ds ++
             filter isExternDecl ds ++
             bindingGroupDecls
    where
      extractGuardedExpr [MkUnguarded expr] = expr
      extractGuardedExpr _ = internalError "Expected Guards to have been desugared in handleDecls."

flattenBindingGroups :: [Declaration] -> [Declaration]
flattenBindingGroups =
  let go (DataBindingGroupDeclaration ds) = NEL.toList ds
      go (BindingGroupDeclaration ds) =
        NEL.toList $ fmap (\((sa, ident), nameKind, val) ->
                             ValueDecl sa ident nameKind [] [MkUnguarded val]) ds
      go other = [other]
  in concatMap go

-- |
-- Collapse all binding groups to individual declarations
--
collapseBindingGroups :: [Declaration] -> [Declaration]
collapseBindingGroups decls =
  let (f, _, _) = everywhereOnValues id collapseBindingGroupsForValue id
      gone = flattenBindingGroups decls
      traversed = fmap f gone
  in traversed


collapseBindingGroupsForValue :: Expr -> Expr
collapseBindingGroupsForValue (Let w ds val) = Let w (flattenBindingGroups ds) val
collapseBindingGroupsForValue other = other

usedIdents :: ModuleName -> ValueDeclarationData Expr -> [Ident]
usedIdents moduleName = ordNub . usedIdents' S.empty . valdeclExpression
  where
  def _ _ = []

  (_, usedIdents', _, _, _) = everythingWithScope def usedNamesE def def def

  usedNamesE :: S.Set ScopedIdent -> Expr -> [Ident]
  usedNamesE scope (Var _ (Qualified Nothing name))
    | LocalIdent name `S.notMember` scope = [name]
  usedNamesE scope (Var _ (Qualified (Just moduleName') name))
    | moduleName == moduleName' && ToplevelIdent name `S.notMember` scope = [name]
  usedNamesE _ _ = []

usedImmediateIdents :: ModuleName -> Declaration -> [Ident]
usedImmediateIdents moduleName =
  let (f, _, _, _, _) = everythingWithContextOnValues True [] (++) def usedNamesE def def def
  in ordNub . f
  where
  def s _ = (s, [])

  usedNamesE :: Bool -> Expr -> (Bool, [Ident])
  usedNamesE True (Var _ (Qualified Nothing name)) = (True, [name])
  usedNamesE True (Var _ (Qualified (Just moduleName') name))
    | moduleName == moduleName' = (True, [name])
  usedNamesE True (Abs _ _) = (False, [])
  usedNamesE scope _ = (scope, [])

usedTypeNames :: ModuleName -> Declaration -> [ProperName 'TypeName]
usedTypeNames moduleName =
  let (f, _, _, _, _) = accumTypes (everythingOnTypes (++) usedNames)
  in ordNub . f
  where
  usedNames :: SourceType -> [ProperName 'TypeName]
  usedNames (ConstrainedType _ con _) =
    case con of
      (Constraint _ (Qualified (Just moduleName') name) _ _)
        | moduleName == moduleName' -> [coerceProperName name]
      _ -> []
  usedNames (TypeConstructor _ (Qualified (Just moduleName') name))
    | moduleName == moduleName' = [name]
  usedNames _ = []

declTypeName :: Declaration -> ProperName 'TypeName
declTypeName (DataDeclaration _ _ pn _ _) = pn
declTypeName (TypeSynonymDeclaration _ pn _ _) = pn
declTypeName _ = internalError "Expected DataDeclaration"

-- |
-- Convert a group of mutually-recursive dependencies into a BindingGroupDeclaration (or simple ValueDeclaration).
--
--
toBindingGroup
  :: forall m
   . (MonadError MultipleErrors m)
   => ModuleName
   -> SCC (ValueDeclarationData Expr)
   -> m Declaration
toBindingGroup _ (AcyclicSCC d) = return (mkDeclaration d)
toBindingGroup moduleName (CyclicSCC ds') = do
  -- Once we have a mutually-recursive group of declarations, we need to sort
  -- them further by their immediate dependencies (those outside function
  -- bodies). In particular, this is relevant for type instance dictionaries
  -- whose members require other type instances (for example, functorEff
  -- defines (<$>) = liftA1, which depends on applicativeEff). Note that
  -- superclass references are still inside functions, so don't count here.
  -- If we discover declarations that still contain mutually-recursive
  -- immediate references, we're guaranteed to get an undefined reference at
  -- runtime, so treat this as an error. See also github issue #365.
  BindingGroupDeclaration . NEL.fromList <$> mapM toBinding (stronglyConnComp valueVerts')
  where
  idents :: [Ident]
  idents = fmap (\(_, i, _) -> i) valueVerts

  valueVerts :: [(ValueDeclarationData Expr, Ident, [Ident])]
  valueVerts = fmap (\d -> (d, valdeclIdent d, usedImmediateIdents moduleName (mkDeclaration d) `intersect` idents)) ds'

  -- Even topological sorting on the immediate dependencies doesn't catch
  -- all of the potential issues: A may immediately evaluate something that
  -- depends on B, and B may have a non-immediate dependency on C. B and C
  -- can appear in any order, but A needs to be defined after both. But just
  -- sorting on the immediate dependencies could leave C defined after A.
  --
  -- So what we *actually* end up looking at is a graph of immediate
  -- dependencies plus some extra edges generated by non-immediate
  -- dependencies. The extra edges from an ident A are to all the idents
  -- that *could* be used by the immediate dependencies of A, ignoring A's
  -- presence in the graph (since it would be impossible for A to use itself
  -- before it is defined, despite being perfectly allowable after).
  --
  -- This algorithm is slightly overcautious; it forbids some relationships
  -- that could be successfully ordered if knowledge about which specific
  -- dependencies were going to be used were taken into account. But it's
  -- precise enough to allow and correctly order the map = liftA1, apply = ap
  -- pattern used in the Effect monad, which is probably good enough.
  valueVerts' :: [(ValueDeclarationData Expr, Vertex, [Vertex])]
  valueVerts' = fmap (\d -> let v = vertFromIdent $ valdeclIdent d in (d, v, valueGraph ! v ++ couldBeUsedBy v)) ds'
    where
    (valueGraph, _, (fromJust .) -> vertFromIdent) = graphFromEdges valueVerts

    nonImmediateEdges :: [(Vertex, Vertex)]
    nonImmediateEdges = do
      d <- ds'
      let v1 = vertFromIdent $ valdeclIdent d
      v2 <- filter (/= v1) . map vertFromIdent . intersect idents $ usedIdents moduleName d
      return (v1, v2)

    couldBeUsedBy :: Vertex -> [Vertex]
    couldBeUsedBy v = filter (/= v) $ reachable couldBeUsedGraph v
      where
      nonImmediateEdges' = filter (\(v1, v2) -> v1 /= v && v2 /= v) nonImmediateEdges
      couldBeUsedGraph = buildG (bounds valueGraph) (map (v,) (valueGraph ! v) ++ nonImmediateEdges')

  toBinding :: SCC (ValueDeclarationData Expr) -> m ((SourceAnn, Ident), NameKind, Expr)
  toBinding (AcyclicSCC d) = return $ fromValueDecl d
  toBinding (CyclicSCC ds) = throwError $ foldMap cycleError ds

  cycleError :: ValueDeclarationData Expr -> MultipleErrors
  cycleError (ValueDeclarationData (ss, _) n _ _ _) = errorMessage' ss $ CycleInDeclaration n

toDataBindingGroup
  :: MonadError MultipleErrors m
  => SCC Declaration
  -> m Declaration
toDataBindingGroup (AcyclicSCC d) = return d
toDataBindingGroup (CyclicSCC [d]) = case isTypeSynonym d of
  Just pn -> throwError . errorMessage' (declSourceSpan d) $ CycleInTypeSynonym (Just pn)
  _ -> return d
toDataBindingGroup (CyclicSCC ds')
  | all (isJust . isTypeSynonym) ds' = throwError . errorMessage' (declSourceSpan (head ds')) $ CycleInTypeSynonym Nothing
  | otherwise = return . DataBindingGroupDeclaration $ NEL.fromList ds'

isTypeSynonym :: Declaration -> Maybe (ProperName 'TypeName)
isTypeSynonym (TypeSynonymDeclaration _ pn _ _) = Just pn
isTypeSynonym _ = Nothing

mkDeclaration :: ValueDeclarationData Expr -> Declaration
mkDeclaration = ValueDeclaration . fmap (pure . MkUnguarded)

fromValueDecl :: ValueDeclarationData Expr -> ((SourceAnn, Ident), NameKind, Expr)
fromValueDecl (ValueDeclarationData sa ident nameKind [] val) = ((sa, ident), nameKind, val)
fromValueDecl ValueDeclarationData{} = internalError "Binders should have been desugared"
