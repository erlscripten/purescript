-- | Optimizer steps for simplifying JavaScript blocks
module Language.PureScript.CoreImp.Optimizer.Blocks
  ( collapseNestedBlocks
  , collapseNestedIfs
  , cleanupBlockStatements
  ) where

import Prelude.Compat
import qualified Data.Map as M
import Data.Maybe
import Language.PureScript.Comments
import Language.PureScript.AST.SourcePos

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
cleanupBlockStatements block = bringBackComments (go noComments) [] where

  stripComments :: [AST]
                -> Int
                -> [([Int], AST)]
                -> M.Map Int [(Maybe SourceSpan, [Comment])]
                -> ([([Int], AST)], M.Map Int [(Maybe SourceSpan, [Comment])])
  stripComments (Comment ss com h : t) n acc strip =
    stripComments (h:t) n acc (M.insertWith (++) n [(ss, com)] strip)
  stripComments (h:t) n acc strip =
    stripComments t (n + 1) (([n], h):acc) strip
  stripComments [] _ acc strip =
    (reverse acc, strip)

  (noComments, comments) = stripComments block 0 [] M.empty

  bringBackComments :: [([Int], AST)] -> [AST] -> [AST]
  bringBackComments [] acc = reverse acc
  bringBackComments ((ids, ast):rest) acc =
    let coms = concat $ mapMaybe (`M.lookup` comments) ids
    in bringBackComments rest (foldr (\(ss, com) r -> Comment ss com r) ast coms : acc)

  go :: [([Int], AST)] -> [([Int], AST)]
  -- TODO: ensure e1 is PURE
  go ((n1, IfElse ss e1 b1 Nothing) : (n2, IfElse _ e2 b2 Nothing) : t)
    | e1 == e2 = go $ (n1 ++ n2, IfElse ss e1 (Block ss Nothing [b1, b2]) Nothing) : t
  go ((n1, IfElse ss1 e1 b1 Nothing):(n2, IfElse ss2 (Binary _ And e2 e3) b2 me) : t)
    | e1 == e2 = go $ (n1 ++ n2, IfElse ss1 e1 (Block ss1 Nothing [b1, IfElse ss2 e3 b2 me]) Nothing) : t
  go ((n1, Block ss l sts1) : (n2, Block _ Nothing sts2) : t) = go $ (n1 ++ n2, Block ss l (sts1 ++ sts2)) : t
  go ((n1, VariableLetIntroduction ss1 name1 Nothing) : (n2, Block _ (Just label1) [Assignment _ (Var _ name2) js, Break _ (Just label2)]) : t)
    | name1 == name2, label1 == label2 = (n1 ++ n2, VariableLetIntroduction ss1 name1 (Just js)) : go t
  go ((n, js@(Return _ _)):_) = [(n, js)]
  go ((n, js@(ReturnNoResult _)):_) = [(n, js)]
  go ((n, js@(Throw _ _)):_) = [(n, js)]
  go ((n, js@(Break _ _)):_) = [(n, js)]
  go ((n, js@(Continue _ _)):_) = [(n, js)]

  go (h:t) = h : go t
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
