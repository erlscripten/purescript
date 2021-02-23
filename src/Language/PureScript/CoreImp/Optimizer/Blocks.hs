-- | Optimizer steps for simplifying JavaScript blocks
module Language.PureScript.CoreImp.Optimizer.Blocks
  ( collapseNestedBlocks
  , collapseNestedIfs
  , cleanupBlockStatements
  ) where

import Prelude.Compat

import Language.PureScript.CoreImp.AST

-- | Collapse blocks which appear nested directly below another block
collapseNestedBlocks :: AST -> AST
collapseNestedBlocks = everywhere collapse where
  collapse :: AST -> AST
  collapse (Block ss n sts) = Block ss n (cleanupBlockStatements $ concatMap go sts)
  collapse js = js

  go :: AST -> [AST]
  go (Block _ Nothing sts) = sts
  go s = [s]

cleanupBlockStatements :: [AST] -> [AST]
cleanupBlockStatements = go where
  go :: [AST] -> [AST]
  -- TODO: ensure e1 is PURE
  go ((IfElse ss e1 b1 Nothing):(IfElse _ e2 b2 Nothing):t) | e1 == e2 = go $ (IfElse ss e1 (Block ss Nothing [b1, b2]) Nothing):t
  go ((IfElse ss1 e1 b1 Nothing):(IfElse ss2 (Binary _ And e2 e3) b2 me):t) | e1 == e2 = go $ (IfElse ss1 e1 (Block ss1 Nothing [b1, IfElse ss2 e3 b2 me]) Nothing):t
  go ((Block ss l sts1):(Block _ Nothing sts2):t) = go $ ((Block ss l (sts1 ++ sts2)):t)
  go ((VariableLetIntroduction ss1 n1 Nothing):(Block _ (Just label1) [Assignment _ (Var _ n2) js, Break _ (Just label2)]):t) | n1 == n2, label1 == label2 = (VariableLetIntroduction ss1 n1 (Just js)):(go t)
  go (js@(Return _ _):_) = [js]
  go (js@(ReturnNoResult _):_) = [js]
  go (js@(Throw _ _):_) = [js]
  go (js@(Break _ _):_) = [js]
  go (js@(Continue _ _):_) = [js]
  go (h:t) = h:(go t)
  go [] = []

collapseNestedIfs :: AST -> AST
collapseNestedIfs = everywhere collapse where
  collapse :: AST -> AST
  collapse (IfElse _ (BooleanLiteral _ True) (Block _ _ [js]) _) = js
  collapse (IfElse _ (BooleanLiteral _ False) _ (Just (Block _ _ [js]))) = js
  collapse (IfElse _ (BooleanLiteral _ True) js _) = js
  collapse (IfElse _ (BooleanLiteral _ False) _ (Just js)) = js
  collapse (IfElse s1 cond1 (Block _ Nothing [IfElse s2 cond2 body Nothing]) Nothing) =
      IfElse s1 (Binary s2 And cond1 cond2) body Nothing
  collapse js = js
