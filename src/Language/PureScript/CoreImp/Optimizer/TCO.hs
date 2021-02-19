-- | This module implements tail call elimination.
module Language.PureScript.CoreImp.Optimizer.TCO (tco) where

import Prelude.Compat

import Debug.Trace

import Control.Monad.State
import Data.Functor ((<&>))
import Data.Text (Text, pack)
import qualified Language.PureScript.Constants as C
import Language.PureScript.CoreImp.AST
import Safe (headDef, tailSafe)

data TCOState = TCOState
  { supply :: !Int
  -- | If there is a variable return right after the block end
  -- then assignment to that variable and breaking will be considered
  -- as a TCO candidate
  , returnBlock :: !(Maybe (Text, Text))
  , tailCalls :: !Int
  }
emptyTCOState :: TCOState
emptyTCOState = TCOState
  { supply = 0
  , returnBlock = Nothing
  , tailCalls = 0
  }

fresh :: State TCOState Int
fresh = do
  x <- gets supply
  modify (\s -> s{supply = x + 1})
  return x

inBlock :: Text -> Text -> State TCOState a -> State TCOState a
inBlock breakL retvar act = do
  prev <- gets returnBlock
  modify' (\s -> s{returnBlock = Just (breakL, retvar)})
  r <- act
  modify' (\s -> s{returnBlock = prev})
  return r

incrTailCount :: State TCOState ()
incrTailCount = modify (\s -> s{tailCalls = tailCalls s + 1})

resetTailCount :: State TCOState ()
resetTailCount = modify (\s -> s{tailCalls = 0})

-- | Eliminate tail calls
tco :: AST -> AST
tco = flip evalState emptyTCOState . everywhereTopDownM convertAST where
  uniq :: Text -> State TCOState Text
  uniq v = fresh <&> \count -> v <>
    if count == 0 then "" else pack . show $ count

  tcoVar :: Text -> Text
  tcoVar arg = "$tco_var_" <> arg

  copyVar :: Text -> Text
  copyVar arg = "$copy_" <> arg

  tcoLoopM :: State TCOState Text
  tcoLoopM = uniq "$tco_loop"

  convertAST :: AST -> State TCOState AST
  convertAST js@(Assignment ass (Var vss name) fn@Function {}) = do
    conv <- convert name fn
    return $ case conv of
      Just looped -> Assignment ass (Var vss name) looped
      _ -> js
  convertAST js = pure js

  convert :: Text -> AST -> State TCOState (Maybe AST)
  convert name fn = do
    let
      innerArgs = headDef [] argss
      outerArgs = concat . reverse $ tailSafe argss
      arity = length argss
      -- ^ this is the number of calls, not the number of arguments, if there's
      -- ever a practical difference.
      (argss, body', replace) = topCollectAllFunctionArgs [] id fn

    looped <- toLoop name arity outerArgs innerArgs body'

    tcs <- gets tailCalls
    resetTailCount
    return $ if tcs == 0
      then Nothing
      else Just $ replace looped

  rewriteFunctionsWith :: ([Text] -> [Text]) -> [[Text]] -> (AST -> AST) -> AST -> ([[Text]], AST, AST -> AST)
  rewriteFunctionsWith argMapper = collectAllFunctionArgs
    where
    collectAllFunctionArgs allArgs f (Function s1 ident args (Block s2 n (body@(Return _ _):_))) =
      collectAllFunctionArgs (args : allArgs) (\b -> f (Function s1 ident (argMapper args) (Block s2 n [b]))) body
    collectAllFunctionArgs allArgs f (Function ss ident args body@Block{}) =
      (args : allArgs, body, f . Function ss ident (argMapper args))
    collectAllFunctionArgs allArgs f (Return s1 (Function s2 ident args (Block s3 n [body]))) =
      collectAllFunctionArgs (args : allArgs) (\b -> f (Return s1 (Function s2 ident (argMapper args) (Block s3 n [b])))) body
    collectAllFunctionArgs allArgs f (Return s1 (Function s2 ident args body@Block{})) =
      (args : allArgs, body, f . Return s1 . Function s2 ident (argMapper args))
    collectAllFunctionArgs allArgs f body = (allArgs, body, f)

  topCollectAllFunctionArgs :: [[Text]] -> (AST -> AST) -> AST -> ([[Text]], AST, AST -> AST)
  topCollectAllFunctionArgs = rewriteFunctionsWith (map copyVar)

  toLoop :: Text -> Int -> [Text] -> [Text] -> AST -> State TCOState AST
  toLoop ident arity outerArgs innerArgs js = do
    tcoLoop <- tcoLoopM

    let
      makeTailJump ss ret = do
        incrTailCount
        let allArgumentValues = concat $ collectArgs [] ret
        return $ Block ss Nothing $
          zipWith (\val arg ->
                     Assignment ss (Var ss (tcoVar arg)) val) allArgumentValues outerArgs
          ++ zipWith (\val arg ->
                        Assignment ss (Var ss (copyVar arg)) val) (drop (length outerArgs) allArgumentValues) innerArgs
          ++ [Continue ss (Just tcoLoop)]

      loopify :: AST -> State TCOState AST
      loopify (Return ss ret) | isSelfCall ident arity ret = makeTailJump ss ret
      loopify (While ss name cond body) = While ss name cond <$> loopify body
      loopify (For ss i js1 js2 body) = For ss i js1 js2 <$> loopify body
      loopify (ForIn ss i js1 body) = ForIn ss i js1 <$> loopify body
      loopify (IfElse ss cond body el) = IfElse ss cond <$> loopify body <*> mapM loopify el
      loopify (Block ss n body) = Block ss n <$> loopifyBlock body
      loopify other = return other

      loopifyBlock :: [AST] -> State TCOState [AST]
      loopifyBlock [] = return []
      loopifyBlock (Block ss (Just n) body : Return _ (Var _ var) : _) =
        (:[]) . Block ss (Just n) <$> inBlock n var (loopifyBlock body)
      loopifyBlock (h1@(Assignment _ (Var _ v) expr) : h2@(Break _ (Just block)) : t) = do
        rb <- gets returnBlock
        case rb of
          Just (rbBlock, rbVar)
            | rbBlock == block, rbVar == v ->
              if isSelfCall ident arity expr
              then (:[]) <$> makeTailJump Nothing expr
              else return [Return Nothing expr]
          _ -> (:) <$> loopify h1 <*> loopifyBlock (h2:t)
      loopifyBlock (h:t) = (:) <$> loopify h <*> loopifyBlock t

    looped <- loopify js

    pure $ Block rootSS Nothing $
        map (\arg -> VariableIntroduction rootSS (tcoVar arg) (Just (Var rootSS (copyVar arg)))) outerArgs ++
        [ While rootSS (Just tcoLoop) (BooleanLiteral Nothing True)
          (Block rootSS Nothing $
            map (\v -> VariableLetIntroduction rootSS v (Just . Var rootSS . tcoVar $ v)) outerArgs ++
            map (\v -> VariableLetIntroduction rootSS v (Just . Var rootSS . copyVar $ v)) innerArgs ++
            [looped]
          )
        ]
    where
    rootSS = Nothing

    collectArgs :: [[AST]] -> AST -> [[AST]]
    collectArgs acc (App _ fn []) =
      -- count 0-argument applications as single-argument so we get the correct number of args
      collectArgs ([Var Nothing C.undefined] : acc) fn
    collectArgs acc (App _ fn args') = collectArgs (args' : acc) fn
    collectArgs acc _ = acc

  isSelfCall :: Text -> Int -> AST -> Bool
  isSelfCall ident 1 (App _ (Var _ ident') _) = ident == ident'
  isSelfCall ident arity (App _ fn _) = isSelfCall ident (arity - 1) fn
  isSelfCall _ _ _ = False
