-- | This module optimizes code in the simplified-JavaScript intermediate representation.
--
-- The following optimizations are supported:
--
--  * Collapsing nested blocks
--
--  * Tail call elimination
--
--  * Inlining of (>>=) and ret for the Eff monad
--
--  * Removal of unnecessary thunks
--
--  * Eta conversion
--
--  * Inlining variables
--
--  * Inline Prelude.($), Prelude.(#), Prelude.(++), Prelude.(!!)
--
--  * Inlining primitive JavaScript operators
module Language.PureScript.CoreImp.Optimizer (optimize, cleanupBlockStatements) where

import Prelude.Compat

import Control.Monad.Supply.Class (MonadSupply)
import Language.PureScript.CoreImp.AST
import Language.PureScript.CoreImp.Optimizer.Blocks
import Language.PureScript.CoreImp.Optimizer.Common
import Language.PureScript.CoreImp.Optimizer.Inliner
import Language.PureScript.CoreImp.Optimizer.MagicDo
import Language.PureScript.CoreImp.Optimizer.TCO
import Language.PureScript.CoreImp.Optimizer.Unused


-- | Apply a series of optimizer passes to simplified JavaScript code
optimize :: MonadSupply m => AST -> m AST
optimize js = do
    let expander = buildExpander js
    js' <- untilFixedPoint (inlineFnComposition expander . inlineFnIdentity expander . inlineUnsafeCoerce . inlineUnsafePartial . tidyUp . applyAll
      [ inlineCommonValues expander
      , inlineCommonOperators expander
      ]) js
    untilFixedPoint (return . tidyUp) . tco . tidyUp . removeUnusedPureVars . inlineST
      =<< untilFixedPoint (return . magicDoST expander)
      =<< untilFixedPoint (return . magicDoEff expander)
      =<< untilFixedPoint (return . magicDoEffect expander) js'
  where
    tidyUp :: AST -> AST
    tidyUp = applyAll
      [ collapseNestedBlocks
      , collapseNestedIfs
      , removeCodeAfterReturnStatements
      , removeUndefinedApp
      , unThunk
      , etaConvert
      , evaluateIifes
      , inlineVariables
      ]

-- |
-- Takes a top level AST and returns a function for expanding local variables
-- during the various inlining steps in `optimize`.
--
-- Everything that gets inlined as an optimization is of a form that would have
-- been lifted to a single outermost Let during CSE, so for purposes of
-- inlining we can save some time by only expanding variables bound at that
-- level and not worrying about any inner scopes.
--
buildExpander :: AST -> AST -> AST
buildExpander (VariableIntroduction _ _ _ (Just (App _ (Function _ Nothing [] (Block _ _ bs)) []))) =
  replaceIdents (foldr f [] bs)
  where
  f (VariableIntroduction _ name IsPure (Just e)) = ((name, e) :)
  f _ = id
buildExpander _ = id

untilFixedPoint :: (Monad m, Eq a) => (a -> m a) -> a -> m a
untilFixedPoint f = go
  where
  go a = do
    a' <- f a
    if a' == a then return a' else go a'
