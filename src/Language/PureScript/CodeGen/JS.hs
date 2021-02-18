-- | This module generates code in the core imperative representation from
-- elaborated PureScript code.
module Language.PureScript.CodeGen.JS
  ( module AST
  , module Common
  , Env(..)
  , moduleToJs
  ) where

import Debug.Trace

import Prelude.Compat
import Protolude (ordNub)

import Control.Arrow ((&&&))
import Control.Monad (forM, replicateM, void)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Reader (MonadReader, asks, local)
import Control.Monad.Supply.Class

import Data.Bifunctor(second, first, bimap)
import Data.List ((\\), intersect)
import qualified Data.Foldable as F
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe, isNothing, mapMaybe)
import Data.String (fromString)
import Data.Text (Text)
import qualified Data.Text as T

import Language.PureScript.AST.SourcePos
import Language.PureScript.CodeGen.JS.Common as Common
import Language.PureScript.CoreImp.AST (AST, everywhereTopDownM, withSourceSpan)
import qualified Language.PureScript.CoreImp.AST as AST
import Language.PureScript.CoreImp.Optimizer
import Language.PureScript.CoreFn
import Language.PureScript.Crash
import Language.PureScript.Errors (ErrorMessageHint(..), SimpleErrorMessage(..),
                                   MultipleErrors(..), rethrow, errorMessage,
                                   errorMessage', rethrowWithPosition, addHint)
import Language.PureScript.Names
import Language.PureScript.Options
import Language.PureScript.PSString (PSString, mkString)
import Language.PureScript.Traversals (sndM)
import qualified Language.PureScript.Constants as C

import System.FilePath.Posix ((</>))

import qualified Data.Map as Map
import Data.Map(Map)

data Env = Env
  { options :: Options
  , vars :: VarEnv
  , continuation :: AST -> AST
  }

type VarEnv = Map Text Text

-- | Generate code in the simplified JavaScript intermediate representation for all declarations in a
-- module.
moduleToJs
  :: forall m
   . (Monad m, MonadReader Env m, MonadSupply m, MonadError MultipleErrors m)
  => Module Ann
  -> Maybe AST
  -> m [AST]
moduleToJs (Module _ coms mn _ imps exps foreigns decls) foreign_ =
  rethrow (addHint (ErrorInModule mn)) $ do
    let usedNames = concatMap getNames decls
    let mnLookup = renameImports usedNames imps
    let decls' = renameModules mnLookup decls

    jsDecls <- inFun $ mapM bindToJs decls'
    optimized <- traverse (traverse optimize) jsDecls
    let mnReverseLookup = M.fromList $ map (\(origName, (_, safeName)) -> (moduleNameToJs safeName, origName)) $ M.toList mnLookup
    let usedModuleNames = foldMap (foldMap (findModules mnReverseLookup)) optimized
    jsImports <- traverse (importToJs mnLookup)
      . filter (`S.member` usedModuleNames)
      . (\\ (mn : C.primModules)) $ ordNub $ map snd imps
    F.traverse_ (F.traverse_ checkIntegers) optimized
    comments <- asks (not . optionsNoComments . options)
    let strict = AST.StringLiteral Nothing "use strict"
    let header = if comments && not (null coms) then AST.Comment Nothing coms strict else strict
    let foreign' = [AST.VariableIntroduction Nothing "$foreign" foreign_ | not $ null foreigns || isNothing foreign_]
    let moduleBody = header : foreign' ++ jsImports ++ concat optimized
    let foreignExps = exps `intersect` foreigns
    let standardExps = exps \\ foreignExps
    let exps' = AST.ObjectLiteral Nothing $ map (mkString . runIdent &&& AST.Var Nothing . identToJs) standardExps
                               ++ map (mkString . runIdent &&& foreignIdent) foreignExps
    return $ moduleBody ++ [AST.Assignment Nothing (accessorString "exports" (AST.Var Nothing "module")) exps']

  where

  inLet :: MonadReader Env m => Text -> Ident -> m a -> m a
  inLet breakRef i = local $ \env ->
    env{continuation = \val ->
        AST.Block Nothing Nothing [AST.Assignment Nothing (var i) val, AST.Break Nothing (Just breakRef)]
       }

  inFun :: MonadReader Env m => m a -> m a
  inFun = local $ \env -> env{continuation = AST.Return Nothing}

  inExpr :: MonadReader Env m => m a -> m a
  inExpr = local $ \env -> env{continuation = \x -> if isExpr x then x else error $ "NOT EXPR: " <> show x} where
    isExpr x = case x of
      AST.Block{} -> False
      AST.Return{} -> False
      AST.VariableIntroduction{} -> False
      AST.VariableLetIntroduction{} -> False
      AST.Label{} -> False
      AST.For{} -> False
      AST.While{} -> False
      AST.IfElse{} -> False
      _ -> True

  -- | Extracts all declaration names from a binding group.
  getNames :: Bind Ann -> [Ident]
  getNames (NonRec _ ident _) = [ident]
  getNames (Rec vals) = map (snd . fst) vals

  -- | Creates alternative names for each module to ensure they don't collide
  -- with declaration names.
  renameImports :: [Ident] -> [(Ann, ModuleName)] -> M.Map ModuleName (Ann, ModuleName)
  renameImports = go M.empty
    where
    go :: M.Map ModuleName (Ann, ModuleName) -> [Ident] -> [(Ann, ModuleName)] -> M.Map ModuleName (Ann, ModuleName)
    go acc used ((ann, mn') : mns') =
      let mni = Ident $ runModuleName mn'
      in if mn' /= mn && mni `elem` used
         then let newName = freshModuleName 1 mn' used
              in go (M.insert mn' (ann, newName) acc) (Ident (runModuleName newName) : used) mns'
         else go (M.insert mn' (ann, mn') acc) used mns'
    go acc _ [] = acc

    freshModuleName :: Integer -> ModuleName -> [Ident] -> ModuleName
    freshModuleName i mn'@(ModuleName name) used =
      let newName = ModuleName $ name <> "_" <> T.pack (show i)
      in if Ident (runModuleName newName) `elem` used
         then freshModuleName (i + 1) mn' used
         else newName

  -- | Generates JavaScript code for a module import, binding the required module
  -- to the alternative
  importToJs :: M.Map ModuleName (Ann, ModuleName) -> ModuleName -> m AST
  importToJs mnLookup mn' = do
    let ((ss, _, _, _), mnSafe) = fromMaybe (internalError "Missing value in mnLookup") $ M.lookup mn' mnLookup
    let moduleBody = AST.App Nothing (AST.Var Nothing "require")
          [AST.StringLiteral Nothing (fromString (".." </> T.unpack (runModuleName mn') </> "index.js"))]
    withPos ss $ AST.VariableIntroduction Nothing (moduleNameToJs mnSafe) (Just moduleBody)

  -- | Replaces the `ModuleName`s in the AST so that the generated code refers to
  -- the collision-avoiding renamed module imports.
  renameModules :: M.Map ModuleName (Ann, ModuleName) -> [Bind Ann] -> [Bind Ann]
  renameModules mnLookup binds =
    let (f, _, _) = everywhereOnValues id goExpr goBinder
    in map f binds
    where
    goExpr :: Expr a -> Expr a
    goExpr (Var ann q) = Var ann (renameQual q)
    goExpr e = e
    goBinder :: Binder a -> Binder a
    goBinder (ConstructorBinder ann q1 q2 bs) = ConstructorBinder ann (renameQual q1) (renameQual q2) bs
    goBinder b = b
    renameQual :: Qualified a -> Qualified a
    renameQual (Qualified (Just mn') a) =
      let (_,mnSafe) = fromMaybe (internalError "Missing value in mnLookup") $ M.lookup mn' mnLookup
      in Qualified (Just mnSafe) a
    renameQual q = q

  -- |
  -- Find the set of ModuleNames referenced by an AST.
  --
  findModules :: M.Map Text ModuleName -> AST -> S.Set ModuleName
  findModules mnReverseLookup = AST.everything mappend go
    where
    go (AST.Var _ name) = foldMap S.singleton $ M.lookup name mnReverseLookup
    go _ = mempty

  -- |
  -- Generate code in the simplified JavaScript intermediate representation for a declaration
  --
  bindToJs :: Bind Ann -> m [AST]
  bindToJs (NonRec ann ident val) = do
    ds <- nonRecToJS ann ident val
    return ds
  bindToJs (Rec vals) = do
    concat <$> forM vals (uncurry . uncurry $ nonRecToJS)

  -- | Generate code in the simplified JavaScript intermediate representation for a single non-recursive
  -- declaration.
  --
  -- The main purpose of this function is to handle code generation for comments.
  nonRecToJS :: Ann -> Ident -> Expr Ann -> m [AST]
  nonRecToJS a i e@(extractAnn -> (_, com, _, _)) | not (null com) = do
    withoutComment <- asks $ optionsNoComments . options
    if withoutComment
       then nonRecToJS a i (modifyAnn removeComments e)
       else map (AST.Comment Nothing com) <$> nonRecToJS a i (modifyAnn removeComments e)
  nonRecToJS (_, _, _, _) ident val = do
    bindToVar ident (valueToJs val)

  withPos :: SourceSpan -> AST -> m AST
  withPos ss js = do
    withSM <- asks (elem JSSourceMap . optionsCodegenTargets . options)
    return $ if withSM
      then withSourceSpan ss js
      else js

  -- | Generate code in the simplified JavaScript intermediate representation for a variable based on a
  -- PureScript identifier.
  var :: Ident -> AST
  var = AST.Var Nothing . identToJs

  -- | Generate code in the simplified JavaScript intermediate representation for an accessor based on
  -- a PureScript identifier. If the name is not valid in JavaScript (symbol based, reserved name) an
  -- indexer is returned.
  accessor :: Ident -> AST -> AST
  accessor (Ident prop) = accessorString $ mkString prop
  accessor (GenIdent _ _) = internalError "GenIdent in accessor"
  accessor UnusedIdent = internalError "UnusedIdent in accessor"

  accessorString :: PSString -> AST -> AST
  accessorString prop = AST.Indexer Nothing (AST.StringLiteral Nothing prop)

  willHandleContinuationByItself :: Expr Ann -> Bool
  willHandleContinuationByItself e = case e of
    Let{} -> True
    Case{} -> True
    _ -> False

  -- | Generate code in the simplified JavaScript intermediate representation for a value or expression.
  valueToJs :: Expr Ann -> m ([AST], AST)
  valueToJs e = do
    let (ss, _, _, _) = extractAnn e
    (ds, x) <- valueToJs' e
    x' <- withPos ss x
    finCont <- asks continuation
    return (ds, if willHandleContinuationByItself e then x' else finCont x')

  single :: AST -> m ([AST], AST)
  single = return . ([],)

  (<$$>) :: (a -> b) -> m ([a], a) -> m ([b], b)
  (<$$>) f m = fmap (bimap (map f) f) m
  traverseCat f l = do
    (ds, vs) <- unzip <$> traverse f l
    return (concat ds, vs)

  bindToVar :: Ident -> m ([AST], AST) -> m [AST]
  bindToVar v ex = do
    breakRef <- freshNameHint $ "def_" <> identToJs v <> "_"
    (ds, js) <- inLet breakRef v ex
    return
      (AST.VariableLetIntroduction Nothing (identToJs v) Nothing :
       ds ++
       [AST.Block Nothing (Just breakRef) [js]]
      )

  valueToJs' :: Expr Ann -> m ([AST], AST)
  valueToJs' (Literal (pos, _, _, _) l) =
    rethrowWithPosition pos $ literalToValueJS pos l
  valueToJs' (Var (_, _, _, Just (IsConstructor _ [])) name) =
    single $ accessorString "value" $ qualifiedToJS id name
  valueToJs' (Var (_, _, _, Just (IsConstructor _ _)) name) =
    single $ accessorString "create" $ qualifiedToJS id name
  valueToJs' (Accessor _ prop val) =
    accessorString prop <$$> inExpr (valueToJs val)
  valueToJs' (ObjectUpdate _ o ps) = do
    (dso, obj) <- inExpr $ valueToJs o
    (dss, sts) <- inExpr $ traverseCat (fmap (\(p, (d, x)) -> (d, (p, x))) . sndM valueToJs) ps
    first ((dso ++ dss) ++) <$> extendObj obj sts
  valueToJs' e@(Abs (_, _, _, Just IsTypeClassConstructor) _ _) = do
    let args = unAbs e
    single $ AST.Function Nothing Nothing (map identToJs args) (AST.Block Nothing Nothing $ map assign args)
    where
    unAbs :: Expr Ann -> [Ident]
    unAbs (Abs _ arg val) = arg : unAbs val
    unAbs _ = []
    assign :: Ident -> AST
    assign name = AST.Assignment Nothing (accessorString (mkString $ runIdent name) (AST.Var Nothing "this"))
                               (var name)
  valueToJs' (Abs _ arg val) = do
    (ds, v) <- inFun $ valueToJs val
    let jsArg = case arg of
                  UnusedIdent -> []
                  _           -> [identToJs arg]
    r <- single $ AST.Function Nothing Nothing jsArg (AST.Block Nothing Nothing $ ds ++ [v])
    return r
  valueToJs' e@App{} = do
    let (f, args) = unApp e []
    (dsa, args') <- inExpr $ traverseCat valueToJs args
    case f of
      Var (_, _, _, Just IsNewtype) _ -> return (dsa, head args')
      Var (_, _, _, Just (IsConstructor _ fields)) name | length args == length fields ->
        return (dsa, AST.Unary Nothing AST.New $ AST.App Nothing (qualifiedToJS id name) args')
      Var (_, _, _, Just IsTypeClassConstructor) name ->
        return (dsa, AST.Unary Nothing AST.New $ AST.App Nothing (qualifiedToJS id name) args')
      _ -> do
        (dsf, v') <- inExpr $ valueToJs f
        return (dsa ++ dsf, foldl (\fn a -> AST.App Nothing fn [a]) v' args')
    where
    unApp :: Expr Ann -> [Expr Ann] -> (Expr Ann, [Expr Ann])
    unApp (App _ val arg) args = unApp val (arg : args)
    unApp other args = (other, args)
  valueToJs' (Var (_, _, _, Just IsForeign) qi@(Qualified (Just mn') ident)) =
    single $ if mn' == mn
             then foreignIdent ident
             else varToJs qi
  valueToJs' (Var (_, _, _, Just IsForeign) ident) =
    internalError $ "Encountered an unqualified reference to a foreign ident " ++ T.unpack (showQualified showIdent ident)
  valueToJs' (Var _ q@(Qualified Nothing (Ident v))) = asks vars >>= \env ->
    single $ case M.lookup v env of
      Nothing -> varToJs q
      Just name -> AST.Var Nothing name
  valueToJs' (Var _ q) = single $ varToJs q
  valueToJs' (Case (ss, _, _, _) values binders) = do
    (ds, vals) <- inExpr $ traverseCat valueToJs values
    resVar <- ("case" <>) . T.pack . show <$> fresh
    dsr <- bindToVar (Ident resVar) (([],) <$> bindersToJs ss binders vals)
    return (ds ++ dsr, AST.Var Nothing resVar)
  valueToJs' (Let _ ds val) = do
    ds' <- inExpr $ concat <$> mapM bindToJs ds
    declsAndMap <- forM ds' $ \d -> case d of
      AST.Var ann name -> do -- FIXME renaming
        q <- freshName
        return (AST.Var ann q, Just (name, q))
      _ -> return (d, Nothing)
    let decls1 = map fst declsAndMap
        env1 = Map.fromList $ mapMaybe snd declsAndMap
    (ds'', ret) <- local (\env -> env{vars = Map.union env1 (vars env)}) $ valueToJs val
    return (decls1 ++ ds'', ret)
  valueToJs' (Constructor (_, _, _, Just IsNewtype) _ ctor _) =
    single $ AST.VariableLetIntroduction Nothing (properToJs ctor) (Just $
                AST.ObjectLiteral Nothing [("create",
                  AST.Function Nothing Nothing ["value"]
                    (AST.Block Nothing Nothing [AST.Return Nothing $ AST.Var Nothing "value"]))])
  valueToJs' (Constructor _ _ ctor []) =
    single $ iife (properToJs ctor) [ AST.Function Nothing (Just (properToJs ctor)) [] (AST.Block Nothing Nothing [])
           , AST.Assignment Nothing (accessorString "value" (AST.Var Nothing (properToJs ctor)))
                (AST.Unary Nothing AST.New $ AST.App Nothing (AST.Var Nothing (properToJs ctor)) []) ]
  valueToJs' (Constructor _ _ ctor fields) =
    let constructor =
          let body = [ AST.Assignment Nothing ((accessorString $ mkString $ identToJs f) (AST.Var Nothing "this")) (var f) | f <- fields ]
          in AST.Function Nothing (Just (properToJs ctor)) (identToJs `map` fields) (AST.Block Nothing Nothing body)
        createFn =
          let body = AST.Unary Nothing AST.New $ AST.App Nothing (AST.Var Nothing (properToJs ctor)) (var `map` fields)
          in foldr (\f inner -> AST.Function Nothing Nothing [identToJs f] (AST.Block Nothing Nothing [AST.Return Nothing inner])) body fields
    in single $ iife (properToJs ctor) [ constructor
                          , AST.Assignment Nothing (accessorString "create" (AST.Var Nothing (properToJs ctor))) createFn
                          ]

  iife :: Text -> [AST] -> AST
  iife v exprs = AST.App Nothing (AST.Function Nothing Nothing [] (AST.Block Nothing  Nothing $ exprs ++ [AST.Return Nothing $ AST.Var Nothing v])) []

  literalToValueJS :: SourceSpan -> Literal (Expr Ann) -> m ([AST], AST)
  literalToValueJS ss (NumericLiteral (Left i)) = single $ AST.NumericLiteral (Just ss) (Left i)
  literalToValueJS ss (NumericLiteral (Right n)) = single $ AST.NumericLiteral (Just ss) (Right n)
  literalToValueJS ss (StringLiteral s) = single $ AST.StringLiteral (Just ss) s
  literalToValueJS ss (CharLiteral c) = single $ AST.StringLiteral (Just ss) (fromString [c])
  literalToValueJS ss (BooleanLiteral b) = single $ AST.BooleanLiteral (Just ss) b
  literalToValueJS ss (ArrayLiteral xs) = do
    (declss, vals) <- traverseCat (inExpr . valueToJs) xs
    return (declss, AST.ArrayLiteral (Just ss) vals)
  literalToValueJS ss (ObjectLiteral ps) = do
    (declss, vals) <- unzip . map (\(p, (d, x)) -> (d, (p, x))) <$> mapM (sndM (inExpr . valueToJs)) ps
    return (concat declss, AST.ObjectLiteral (Just ss) vals)

  -- | Shallow copy an object.
  extendObj :: AST -> [(PSString, AST)] -> m ([AST], AST)
  extendObj obj sts = do
    newObj <- freshName
    key <- freshName
    evaluatedObj <- freshName
    let
      jsKey = AST.Var Nothing key
      jsNewObj = AST.Var Nothing newObj
      jsEvaluatedObj = AST.Var Nothing evaluatedObj
      evaluate = AST.VariableLetIntroduction Nothing evaluatedObj (Just obj)
      objAssign = AST.VariableLetIntroduction Nothing newObj (Just $ AST.ObjectLiteral Nothing [])
      copy = AST.ForIn Nothing key jsEvaluatedObj $ AST.Block Nothing Nothing [AST.IfElse Nothing cond assign Nothing]
      cond = AST.App Nothing (accessorString "call" (accessorString "hasOwnProperty" (AST.ObjectLiteral Nothing []))) [jsEvaluatedObj, jsKey]
      assign = AST.Block Nothing Nothing [AST.Assignment Nothing (AST.Indexer Nothing jsKey jsNewObj) (AST.Indexer Nothing jsKey jsEvaluatedObj)]
      stToAssign (s, js) = AST.Assignment Nothing (accessorString s jsNewObj) js
      extend = map stToAssign sts
    return (evaluate:objAssign:copy:extend, jsNewObj)

  -- | Generate code in the simplified JavaScript intermediate representation for a reference to a
  -- variable.
  varToJs :: Qualified Ident -> AST
  varToJs (Qualified Nothing ident) = var ident
  varToJs qual = qualifiedToJS id qual

  -- | Generate code in the simplified JavaScript intermediate representation for a reference to a
  -- variable that may have a qualified name.
  qualifiedToJS :: (a -> Ident) -> Qualified a -> AST
  qualifiedToJS f (Qualified (Just C.Prim) a) = AST.Var Nothing . runIdent $ f a
  qualifiedToJS f (Qualified (Just mn') a) | mn /= mn' = accessor (f a) (AST.Var Nothing (moduleNameToJs mn'))
  qualifiedToJS f (Qualified _ a) = AST.Var Nothing $ identToJs (f a)

  foreignIdent :: Ident -> AST
  foreignIdent ident = accessorString (mkString $ runIdent ident) (AST.Var Nothing "$foreign")

  -- | Generate code in the simplified JavaScript intermediate representation for pattern match binders
  -- and guards.
  bindersToJs :: SourceSpan -> [CaseAlternative Ann] -> [AST] -> m AST
  bindersToJs ss alts vals = do
    valNames <- replicateM (length vals) freshName
    let assignments = zipWith (AST.VariableLetIntroduction Nothing) valNames (map Just vals)
    jss <- forM alts $ \(CaseAlternative bs result) -> do
      ret <- guardsToJs result
      go valNames ret bs
    return $ AST.Block Nothing Nothing (assignments ++ concat jss ++ [AST.Throw Nothing $ failedPatternError valNames])
    where
      go :: [Text] -> [AST] -> [Binder Ann] -> m [AST]
      go _ done [] = return done
      go (v:vs) done' (b:bs) = do
        done'' <- go vs done' bs
        binderToJs v done'' b
      go _ _ _ = internalError "Invalid arguments to bindersToJs"

      failedPatternError :: [Text] -> AST
      failedPatternError names = AST.Unary Nothing AST.New $ AST.App Nothing (AST.Var Nothing "Error") [AST.Binary Nothing AST.Add (AST.StringLiteral Nothing $ mkString failedPatternMessage) (AST.ArrayLiteral Nothing $ zipWith valueError names vals)]

      failedPatternMessage :: Text
      failedPatternMessage = "Failed pattern match at " <> runModuleName mn <> " " <> displayStartEndPos ss <> ": "

      valueError :: Text -> AST -> AST
      valueError _ l@(AST.NumericLiteral _ _) = l
      valueError _ l@(AST.StringLiteral _ _)  = l
      valueError _ l@(AST.BooleanLiteral _ _) = l
      valueError s _                          = accessorString "name" . accessorString "constructor" $ AST.Var Nothing s

      guardsToJs :: Either [([Guard Ann], Expr Ann)] (Expr Ann) -> m [AST]
      guardsToJs (Left gs) = do
        let genGuard :: ([Guard Ann], Expr Ann) -> m AST
            genGuard (conds, val) = do
              rollback <- freshName
              guardSeqJs <- guardSeqToJs (Just rollback) conds val
              return $ AST.Block Nothing (Just rollback) guardSeqJs
        traverse genGuard gs
      guardsToJs (Right v) = do
        guardSeqToJs Nothing [] v

      guardSeqToJs :: Maybe Text -> [Guard Ann] -> Expr Ann -> m [AST]
      guardSeqToJs _ [] fin = do
        (ds, fin') <- valueToJs fin
        return $ ds ++ [fin']
      guardSeqToJs rollback (ConditionGuard e : rest) fin = do
         (ds, val) <- inExpr $ valueToJs e
         cont <- guardSeqToJs rollback rest fin
         return $ ds ++
           [ AST.IfElse Nothing val (AST.Block Nothing Nothing cont)
             (AST.Break Nothing . Just <$> rollback)
           ]
      guardSeqToJs rollback (PatternGuard lv rv : rest) fin = do
         (ds, rv') <- inExpr $ valueToJs rv
         casevar <- freshName
         cont <- guardSeqToJs rollback rest fin
         bind <- binderToJs casevar cont lv
         return $ ds ++ [AST.VariableLetIntroduction Nothing casevar (Just rv')] ++ bind ++ maybe [] ((:[]) . AST.Break Nothing . Just) rollback

  binderToJs :: Text -> [AST] -> Binder Ann -> m [AST]
  binderToJs s done binder =
    let (ss, _, _, _) = extractBinderAnn binder in
    traverse (withPos ss) =<< binderToJs' s done binder

  -- | Generate code in the simplified JavaScript intermediate representation for a pattern match
  -- binder.
  binderToJs' :: Text -> [AST] -> Binder Ann -> m [AST]
  binderToJs' _ done NullBinder{} = return done
  binderToJs' varName done (LiteralBinder _ l) =
    literalToBinderJS varName done l
  binderToJs' varName done (VarBinder _ ident) =
    return (AST.VariableLetIntroduction Nothing (identToJs ident) (Just (AST.Var Nothing varName)) : done)
  binderToJs' varName done (ConstructorBinder (_, _, _, Just IsNewtype) _ _ [b]) =
    binderToJs varName done b
  binderToJs' varName done (ConstructorBinder (_, _, _, Just (IsConstructor ctorType fields)) _ ctor bs) = do
    js <- go (zip fields bs) done
    return $ case ctorType of
      ProductType -> js
      SumType ->
        [AST.IfElse Nothing (AST.InstanceOf Nothing (AST.Var Nothing varName) (qualifiedToJS (Ident . runProperName) ctor))
                  (AST.Block Nothing Nothing js)
                  Nothing]
    where
    go :: [(Ident, Binder Ann)] -> [AST] -> m [AST]
    go [] done' = return done'
    go ((field, binder) : remain) done' = do
      argVar <- freshName
      done'' <- go remain done'
      js <- binderToJs argVar done'' binder
      return (AST.VariableLetIntroduction Nothing argVar (Just $ accessorString (mkString $ identToJs field) $ AST.Var Nothing varName) : js)
  binderToJs' _ _ ConstructorBinder{} =
    internalError "binderToJs: Invalid ConstructorBinder in binderToJs"
  binderToJs' varName done (NamedBinder _ ident binder) = do
    js <- binderToJs varName done binder
    return (AST.VariableLetIntroduction Nothing (identToJs ident) (Just (AST.Var Nothing varName)) : js)

  literalToBinderJS :: Text -> [AST] -> Literal (Binder Ann) -> m [AST]
  literalToBinderJS varName done (NumericLiteral num) =
    return [AST.IfElse Nothing (AST.Binary Nothing AST.EqualTo (AST.Var Nothing varName) (AST.NumericLiteral Nothing num)) (AST.Block Nothing Nothing done) Nothing]
  literalToBinderJS varName done (CharLiteral c) =
    return [AST.IfElse Nothing (AST.Binary Nothing AST.EqualTo (AST.Var Nothing varName) (AST.StringLiteral Nothing (fromString [c]))) (AST.Block Nothing Nothing done) Nothing]
  literalToBinderJS varName done (StringLiteral str) =
    return [AST.IfElse Nothing (AST.Binary Nothing AST.EqualTo (AST.Var Nothing varName) (AST.StringLiteral Nothing str)) (AST.Block Nothing Nothing done) Nothing]
  literalToBinderJS varName done (BooleanLiteral True) =
    return [AST.IfElse Nothing (AST.Var Nothing varName) (AST.Block Nothing Nothing done) Nothing]
  literalToBinderJS varName done (BooleanLiteral False) =
    return [AST.IfElse Nothing (AST.Unary Nothing AST.Not (AST.Var Nothing varName)) (AST.Block Nothing Nothing done) Nothing]
  literalToBinderJS varName done (ObjectLiteral bs) = go done bs
    where
    go :: [AST] -> [(PSString, Binder Ann)] -> m [AST]
    go done' [] = return done'
    go done' ((prop, binder):bs') = do
      propVar <- freshName
      done'' <- go done' bs'
      js <- binderToJs propVar done'' binder
      return (AST.VariableLetIntroduction Nothing propVar (Just (accessorString prop (AST.Var Nothing varName))) : js)
  literalToBinderJS varName done (ArrayLiteral bs) = do
    js <- go done 0 bs
    return [AST.IfElse Nothing (AST.Binary Nothing AST.EqualTo (accessorString "length" (AST.Var Nothing varName)) (AST.NumericLiteral Nothing (Left (fromIntegral $ length bs)))) (AST.Block Nothing Nothing js) Nothing]
    where
    go :: [AST] -> Integer -> [Binder Ann] -> m [AST]
    go done' _ [] = return done'
    go done' index (binder:bs') = do
      elVar <- freshName
      done'' <- go done' (index + 1) bs'
      js <- binderToJs elVar done'' binder
      return (AST.VariableLetIntroduction Nothing elVar (Just (AST.Indexer Nothing (AST.NumericLiteral Nothing (Left index)) (AST.Var Nothing varName))) : js)

  -- Check that all integers fall within the valid int range for JavaScript.
  checkIntegers :: AST -> m ()
  checkIntegers = void . everywhereTopDownM go
    where
    go :: AST -> m AST
    go (AST.Unary _ AST.Negate (AST.NumericLiteral ss (Left i))) =
      -- Move the negation inside the literal; since this is a top-down
      -- traversal doing this replacement will stop the next case from raising
      -- the error when attempting to use -2147483648, as if left unrewritten
      -- the value is `Unary Negate (NumericLiteral (Left 2147483648))`, and
      -- 2147483648 is larger than the maximum allowed int.
      return $ AST.NumericLiteral ss (Left (-i))
    go js@(AST.NumericLiteral ss (Left i)) =
      let minInt = -2147483648
          maxInt = 2147483647
      in if i < minInt || i > maxInt
         then throwError . maybe errorMessage errorMessage' ss $ IntOutOfRange i "JavaScript" minInt maxInt
         else return js
    go other = return other
