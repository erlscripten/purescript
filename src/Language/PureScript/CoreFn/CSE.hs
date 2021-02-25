{-# LANGUAGE TemplateHaskell #-}
-- | This module performs limited common subexpression elimination
module Language.PureScript.CoreFn.CSE (optimizeCommonSubexpressions) where

import Protolude hiding (pass)

import Control.Monad.Supply (Supply)
import Control.Monad.Supply.Class (MonadSupply)
import Control.Monad.RWS (MonadWriter, RWST, censor, evalRWST, listen, pass, tell)
import Data.Bitraversable (bitraverse)
import Data.Functor.Compose (Compose(..))
import Data.Semigroup (Min(..))
import Data.Semigroup.Generic (gmappend, gmempty)
import Data.Maybe (fromJust)
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Map as M
import Lens.Micro.Platform

import Language.PureScript.AST.Literals
import Language.PureScript.AST.SourcePos (nullSourceSpan)
import Language.PureScript.CoreFn.Ann (Ann)
import Language.PureScript.CoreFn.Binders
import Language.PureScript.CoreFn.Expr
import Language.PureScript.CoreFn.Meta (Meta(IsSyntheticApp))
import Language.PureScript.CoreFn.Traversals
import Language.PureScript.Names
import Language.PureScript.PSString (decodeString)
import qualified Language.PureScript.Constants as C

-- |
-- `discuss f m` is an action that listens to the output of `m`, passes that
-- and its value through `f`, and uses (only) the value of the result to set
-- the new value and output. (Any output produced via the monad in `f` is
-- ignored, though other monadic effects will hold.)
--
discuss :: MonadWriter w m => ((a, w) -> m (b, w)) -> m a -> m b
discuss f = pass . fmap (fmap const) . (>>= f) . listen

-- |
-- Modifies the target of an optic in the state with a monadic computation that
-- returns some extra information in a tuple.
--
-- This is a made-up lens operator adapting (%%=) from the lens package to
-- support wrapping the returned tuple in the monad. It's a little dangerous in
-- that it doesn't prevent making modifications to the state from within the
-- computation, which will all be overwritten by the state coming out of the
-- lens; don't do that.
--
(%%<~) :: MonadState s m
       => ((a -> Compose m ((,) r) b)
       -> s
       -> Compose m ((,) r) s)
       -> (a -> m (r, b))
       -> m r
l %%<~ f = get >>= getCompose . l (Compose . f) >>= state . const
infix 4 %%<~

-- |
-- A PluralityMap is like a weaker multiset: like a multiset, it holds a
-- number of values, but instead of keeping track of their exact counts, it
-- only records whether there is one (False) or more than one (True).
--
newtype PluralityMap k = PluralityMap { getPluralityMap :: M.Map k Bool }

instance Ord k => Semigroup (PluralityMap k) where
  PluralityMap l <> PluralityMap r =
    PluralityMap $ M.mapWithKey (\k -> (|| k `M.member` r)) l `M.union` r

instance Ord k => Monoid (PluralityMap k) where
  mempty = PluralityMap M.empty

-- |
-- A ScopeMap is just a newtype wrapper around an IntMap that has a
-- Semigroup instance respecting the Semigroup of the underlying
-- value. It's used here to represent information that can be accessed and
-- discarded by scope depth, hence the name.
--
newtype ScopeMap v = ScopeMap { getScopeMap :: IM.IntMap v }

-- |
-- Appends a value at a given scope depth.
--
addToScope :: Semigroup v => Int -> v -> ScopeMap v -> ScopeMap v
addToScope depth v = ScopeMap
                   . IM.alter (Just . maybe v (<> v)) depth
                   . getScopeMap

-- |
-- Removes and returns an entire scope from the ScopeMap.
--
popScope :: Monoid v => Int -> ScopeMap v -> (v, ScopeMap v)
popScope depth = bimap fold ScopeMap
               . IM.updateLookupWithKey (\_ _ -> Nothing) depth
               . getScopeMap

instance Semigroup v => Semigroup (ScopeMap v) where
  ScopeMap l <> ScopeMap r = ScopeMap $ IM.unionWith (<>) l r

instance Semigroup v => Monoid (ScopeMap v) where
  mempty = ScopeMap IM.empty

data BindingType = NonRecursive | Recursive deriving Eq

-- |
-- Records summary data about an expression.
--
data CSESummary = CSESummary
  { _scopesUsed    :: IS.IntSet
    -- ^ set of the scope numbers used in this expression
  , _noFloatWithin :: Maybe (Min Int)
    -- ^ optionally a scope within which this expression is not to be floated
    -- (because the expression uses an identifier bound recursively in that
    -- scope)
  , _plurality     :: PluralityMap Ident
    -- ^ which floated identifiers are used more than once in this expression
    -- (note that a single use inside an Abs will be considered multiple uses,
    -- as this pass doesn't know when/how many times an Abs will be executed)
  , _newBindings   :: ScopeMap [(Ident, (PluralityMap Ident, Expr Ann))]
    -- ^ floated bindings, organized by scope number
  , _toBeReinlined :: M.Map Ident (Expr Ann)
    -- ^ a map of floated identifiers that did not end up getting bound and
    -- will need to be reinlined at the end of the pass
  } deriving Generic

instance Semigroup CSESummary where
  (<>) = gmappend

instance Monoid CSESummary where
  mempty = gmempty

-- |
-- Describes the context of an expression.
--
data CSEEnvironment = CSEEnvironment
  { _depth :: Int
    -- ^ number of enclosing binding scopes (this includes not only Abs, but
    -- Let and CaseAlternative bindings)
  , _bound :: M.Map Ident (Int, BindingType)
    -- ^ map from identifiers to depth in which they are bound and whether
    -- or not the binding is recursive
  }

makeLenses ''CSESummary
makeLenses ''CSEEnvironment

-- |
-- Maps from the shape of an expression to an identifier created to represent
-- that expression, organized by scope depth.
--
type CSEState = IM.IntMap (M.Map (Expr ()) Ident)

-- |
-- The monad in which CSE takes place.
--
type CSEMonad a = RWST CSEEnvironment CSESummary CSEState Supply a

type HasCSEReader = MonadReader CSEEnvironment
type HasCSEWriter = MonadWriter CSESummary
type HasCSEState = MonadState CSEState

-- |
-- Runs a CSEMonad computation given a list of top-level identifiers; the
-- return value is augmented with a map of identifiers that should be replaced
-- in the final expression because they didn't end up needing to be floated.
--
evalCSEMonad :: [Ident] -> CSEMonad a -> Supply (a, M.Map Ident (Expr Ann))
evalCSEMonad recursiveIdents x =
  fmap (fmap (^. toBeReinlined)) $ evalRWST x (CSEEnvironment 0 initBound) IM.empty
  where
  initBound = M.fromList . map (, (0, Recursive)) $ recursiveIdents

-- |
-- Marks all expressions floated out of this computation as "plural". This pass
-- assumes that any given Abs may be invoked multiple times, so any expressions
-- inside the Abs but floated out of it also count as having multiple uses,
-- even if they only appear once within the Abs. Consequently, any expressions
-- that can be floated out of an Abs won't be reinlined at the end.
--
enterAbs :: HasCSEWriter m => m a -> m a
enterAbs = censor $ plurality %~ PluralityMap . fmap (const True) . getPluralityMap

-- |
-- Runs the provided computation in a new scope.
--
newScope :: (HasCSEReader m, HasCSEWriter m) => (Int -> m a) -> m a
newScope body = local (depth %~ (+ 1)) $ do
  d <- view depth
  censor (filterToDepth d) (body d)
  where
  filterToDepth d = (scopesUsed %~ IS.filter (< d))
                  . (noFloatWithin %~ find (< Min d))

-- |
-- Records a list of identifiers as being bound in the given scope.
--
withBoundIdents :: HasCSEReader m => [Ident] -> (Int, BindingType) -> m a -> m a
withBoundIdents idents t = local (bound %~ flip (foldl' (flip (flip M.insert t))) idents)

-- |
-- Runs the provided computation in a new scope in which the provided
-- identifiers are bound non-recursively.
--
newScopeWithIdents :: (HasCSEReader m, HasCSEWriter m) => [Ident] -> m a -> m a
newScopeWithIdents idents = newScope . (flip $ withBoundIdents idents . (, NonRecursive))

-- |
-- Produces, or retrieves from the state, an identifier for referencing the
-- given expression, at and below the given depth.
--
generateIdentFor :: (HasCSEState m, MonadSupply m) => Int -> Expr () -> m (Bool, Ident)
generateIdentFor d e = at d . non mempty . at e %%<~ \case
  Nothing    -> do
                ident <- freshIdent (nameHint e)
                return ((True, ident), Just ident)
  Just ident -> return ((False, ident), Just ident)
  where
  nameHint = \case
    App _ v1 v2
      | Var _ (fmap (ProperName . runIdent) -> C.IsSymbol) <- v1
      , Abs _ _ (Literal _ (StringLiteral str)) <- v2
      , Just decodedStr <- decodeString str
        -> decodedStr <> "IsSymbol"
      | otherwise
        -> nameHint v1
    Var _ (Qualified _ ident)
      | Ident name             <- ident -> name
      | GenIdent (Just name) _ <- ident -> name
    Accessor _ prop _
      | Just decodedProp <- decodeString prop -> decodedProp
    _ -> "ref"

nullAnn :: Ann
nullAnn = (nullSourceSpan, [], Nothing, Nothing)

-- |
-- Uses a map to substitute local Vars in an expression.
--
replaceLocals :: M.Map Ident (Expr Ann) -> Expr Ann -> Expr Ann
replaceLocals m = if M.null m then identity else f' where
  (_, f', _) = everywhereOnValues identity f identity
  f e@(Var _ (Qualified Nothing ident)) = maybe e f' $ M.lookup ident m
  f e = e

mkNonRec :: (Ident, Expr Ann) -> Bind Ann
mkNonRec = uncurry (NonRec nullAnn)

-- |
-- Stores in the monad a new binding for the given expression, returning a Var
-- referencing it. The provided CSESummary will be transformed to reflect the
-- replacement.
--
floatExpr :: (HasCSEState m, MonadSupply m)
          => (Expr Ann, CSESummary)
          -> m (Expr Ann, CSESummary)
floatExpr = \case
  (e, w@CSESummary{ _noFloatWithin = Nothing, .. }) -> do
    let deepestScope = if IS.null _scopesUsed then 0 else IS.findMax _scopesUsed
    (isNew, ident) <- generateIdentFor deepestScope (void e)
    let w' = if isNew
             then w & newBindings %~ addToScope deepestScope [(ident, (_plurality, e))]
             else w
        w'' = w' & plurality .~ PluralityMap (M.singleton ident False)
    return (Var nullAnn (Qualified Nothing ident), w'')
  (e, w) -> return (e, w)

-- |
-- Takes possession of the bindings intended to be added to the current scope,
-- removing them from the state. Returns the list of bindings along with whatever
-- value is returned by the provided computation.
--
getNewBindings :: (HasCSEReader m, HasCSEState m, HasCSEWriter m)
               => m a
               -> m ([(Ident, Expr Ann)], a)
getNewBindings = discuss $ \(a, w) -> do
  d <- view depth
  at d .= Nothing
  let (floatedHere, w') = newBindings (popScope d) w
  return $ first (, a) $ foldr handleFloat (mempty, w') floatedHere
  where
  handleFloat (ident, (p, e)) (bs, w) =
    if fromJust . M.lookup ident . getPluralityMap $ w ^. plurality
    then ((ident, e) : bs, w')
    else (bs, w' & toBeReinlined %~ M.insert ident e)
    where w' = w & plurality <>~ p

-- |
-- Like getNewBindings, but also stores the bindings in a Let wrapping the
-- provided expression. If said expression is already a Let, adds these
-- bindings to that Let instead.
--
getNewBindingsAsLet :: (HasCSEReader m, HasCSEWriter m, HasCSEState m)
                    => m (Expr Ann)
                    -> m (Expr Ann)
getNewBindingsAsLet = fmap (uncurry go) . getNewBindings where
  go bs = if null bs then identity else mergeLets $ map mkNonRec bs
  mergeLets :: [Bind Ann] -> Expr Ann -> Expr Ann
  mergeLets bs = \case
    Let a bs' e' -> Let a (bs ++ bs') e'
    e'           -> Let nullAnn bs e'

-- |
-- Feeds the Writer part of the monad with the requirements of this name.
--
summarizeName :: (HasCSEReader m, HasCSEWriter m)
              => ModuleName
              -> Qualified Ident
              -> m ()
summarizeName mn (Qualified mn' ident) = do
  m <- view bound
  let (s, bt) = fromMaybe (0, NonRecursive) $
                  guard (all (== mn) mn') *> M.lookup ident m
  tell $ mempty
       & scopesUsed .~ IS.singleton s
       & noFloatWithin .~ if bt == NonRecursive then Nothing else Just (Min s)

-- |
-- Collects all the Idents put in scope by a list of Binders.
--
identsFromBinders :: [Binder a] -> [Ident]
identsFromBinders = foldMap identsFromBinder where
  identsFromBinder = \case
    LiteralBinder _ (ArrayLiteral xs)  -> identsFromBinders xs
    LiteralBinder _ (ObjectLiteral xs) -> identsFromBinders (map snd xs)
    VarBinder _ ident                  -> [ident]
    ConstructorBinder _ _ _ xs         -> identsFromBinders xs
    NamedBinder _ ident x              -> ident : identsFromBinder x
    _                                  -> []

-- |
-- Floats synthetic Apps (right now, the only Apps marked as synthetic are type
-- class dictionaries being fed to functions with constraints, superclass
-- accessors, and instances of IsSymbol) to a new or existing Let as close to
-- the top level as possible.
--
optimizeCommonSubexpressions :: ModuleName -> [Bind Ann] -> Supply [Bind Ann]
optimizeCommonSubexpressions mn = traverse $ \case
  NonRec a n e -> NonRec a n <$> traverseTopExpr [] e
  Rec es       -> Rec <$> traverse (traverse (traverseTopExpr (map (snd . fst) es))) es

  where

  -- This is the one place (I think?) that keeps this from being a general
  -- common subexpression elimination pass.
  shouldFloatExpr :: Expr Ann -> Bool
  shouldFloatExpr = \case
    App (_, _, _, Just IsSyntheticApp) e _ -> isSimple e
    _                                      -> False

  isSimple :: Expr Ann -> Bool
  isSimple = \case
    Var{}          -> True
    Accessor _ _ e -> isSimple e
    _              -> False

  -- Top-level bindings are processed specially because Renamer gets cranky if
  -- any GenIdents get out. In theory, this could be changed, and then
  -- traverseBinds would be used to handle all of the top-level bindings
  -- together.
  traverseTopExpr :: [Ident] -> Expr Ann -> Supply (Expr Ann)
  traverseTopExpr recursiveIdents = fmap (uncurry (flip replaceLocals))
                                  . evalCSEMonad recursiveIdents
                                  . traverseAndWrapExpr

  traverseAndWrapExpr :: Expr Ann -> CSEMonad (Expr Ann)
  traverseAndWrapExpr = getNewBindingsAsLet . traverseExpr

  traverseExpr :: Expr Ann -> CSEMonad (Expr Ann)
  traverseExpr = discuss (ifM (shouldFloatExpr . fst) floatExpr return) . \case
    Abs a ident e         -> enterAbs $ Abs a ident <$> newScopeWithIdents [ident] (traverseAndWrapExpr e)

    v@(Var _ qname)       -> summarizeName mn qname $> v

    Let a bs e            -> uncurry (Let a) <$> traverseBinds (traverseExpr e) bs
    Case a vs alts        -> Case a <$> traverse traverseExpr vs <*> traverse traverseCaseAlternative alts

    Literal a l           -> Literal a <$> traverseLiteral l
    Accessor a prop e     -> Accessor a prop <$> traverseExpr e
    ObjectUpdate a obj vs -> ObjectUpdate a <$> traverseExpr obj <*> traverse (traverse traverseExpr) vs
    App a v1 v2           -> App a <$> traverseExpr v1 <*> traverseExpr v2
    x                     -> return x

  traverseCaseAlternative :: CaseAlternative Ann -> CSEMonad (CaseAlternative Ann)
  traverseCaseAlternative (CaseAlternative bs x) = CaseAlternative bs <$> do
    newScopeWithIdents (identsFromBinders bs) $
      bitraverse (traverse $ bitraverse (traverse traverseAndWrapExpr) traverseAndWrapExpr) traverseAndWrapExpr x

  traverseLiteral :: Literal (Expr Ann) -> CSEMonad (Literal (Expr Ann))
  traverseLiteral = \case
    ArrayLiteral xs  -> ArrayLiteral <$> traverse traverseExpr xs
    ObjectLiteral xs -> ObjectLiteral <$> traverse (traverse traverseExpr) xs
    x                -> return x

  traverseBinds :: forall a. CSEMonad a -> [Bind Ann] -> CSEMonad ([Bind Ann], a)
  traverseBinds end = foldr f (fmap pure end) where
    f b inner = case b of
      -- For a NonRec Bind, traverse the bound expression in the current scope
      -- and then create a new scope for any remaining Binds and/or whatever
      -- inner thing all these Binds are applied to.
      NonRec a ident e -> do
        e' <- traverseExpr e
        newScopeWithIdents [ident] $
          addNewBindsFromInner $ \bs -> (NonRec a ident e' :) . (map mkNonRec bs ++)
      Rec es ->
        -- For a Rec Bind, the bound expressions need a new scope in which all
        -- these identifiers are bound recursively; then the remaining Binds
        -- and the inner thing can be traversed in the same scope with the same
        -- identifiers now bound non-recursively.
        newScope $ \d -> do
          let idents = map (snd . fst) es
          es' <- withBoundIdents idents (d, Recursive) $ traverse (traverse traverseExpr) es
          withBoundIdents idents (d, NonRecursive) $
            addNewBindsFromInner $ \bs -> (Rec (map (first (nullAnn,)) bs ++ es') :)

      where

      addNewBindsFromInner :: ([(Ident, Expr Ann)] -> [Bind Ann] -> [Bind Ann])
                           -> CSEMonad ([Bind Ann], a)
      addNewBindsFromInner prependToBinds =
        uncurry (first . prependToBinds) <$> getNewBindings inner
