{-# LANGUAGE Strict #-}
-- | Common functions used by the various optimizer phases
module Language.PureScript.CoreImp.Optimizer.Common where

import Prelude.Compat

import Data.Text (Text)
import Data.List (foldl')
import Data.Maybe (fromMaybe)

import Language.PureScript.Crash
import Language.PureScript.CoreImp.AST
import Language.PureScript.PSString (PSString)

{-# INLINE applyAll #-}
applyAll :: [a -> a] -> a -> a
applyAll l x = foldl' (flip ($!)) x l

{-# INLINE replaceIdent #-}
replaceIdent :: Text -> AST -> AST -> AST
replaceIdent var1 js = everywhere replace
  where
  replace (Var _ var2) | var1 == var2 = js
  replace other = other

{-# INLINE replaceIdents #-}
replaceIdents :: [(Text, AST)] -> AST -> AST
replaceIdents vars = everywhere replace
  where
  replace v@(Var _ var) = fromMaybe v $ lookup var vars
  replace other = other

{-# INLINE isReassigned #-}
isReassigned :: Text -> AST -> Bool
isReassigned var1 = everything (||) check
  where
  check :: AST -> Bool
  check (Function _ _ args _) | var1 `elem` args = True
  check (VariableIntroduction _ arg _ _) | var1 == arg = True
  check (VariableLetIntroduction _ arg _ _) | var1 == arg = True
  check (Assignment _ (Var _ arg) _) | var1 == arg = True
  check (For _ arg _ _ _) | var1 == arg = True
  check (ForIn _ arg _ _) | var1 == arg = True
  check _ = False

{-# INLINE isRebound #-}
isRebound :: AST -> AST -> Bool
isRebound js d = any (\v -> isReassigned v d || isUpdated v d) (everything (++) variablesOf js)
  where
  variablesOf (Var _ var) = [var]
  variablesOf _ = []

{-# INLINE isUsed #-}
isUsed :: Text -> AST -> Bool
isUsed var1 = everything (||) check
  where
  check :: AST -> Bool
  check (Var _ var2) | var1 == var2 = True
  check (Assignment _ target _) | var1 == targetVariable target = True
  check _ = False

{-# INLINE targetVariable #-}
targetVariable :: AST -> Text
targetVariable (Var _ var) = var
targetVariable (Indexer _ _ tgt) = targetVariable tgt
targetVariable _ = internalError "Invalid argument to targetVariable"

{-# INLINE isUpdated #-}
isUpdated :: Text -> AST -> Bool
isUpdated var1 = everything (||) check
  where
  check :: AST -> Bool
  check (Assignment _ target _) | var1 == targetVariable target = True
  check _ = False

{-# INLINE removeFromBlock #-}
removeFromBlock :: ([AST] -> [AST]) -> AST -> AST
removeFromBlock go (Block ss n sts) = Block ss n (go sts)
removeFromBlock _  js = js

{-# INLINE isDict #-}
isDict :: (Text, PSString) -> AST -> Bool
isDict (moduleName, dictName) (Indexer _ (StringLiteral _ x) (Var _ y)) =
  x == dictName && y == moduleName
isDict _ _ = False

{-# INLINE isDict' #-}
isDict' :: [(Text, PSString)] -> AST -> Bool
isDict' xs js = any (`isDict` js) xs
