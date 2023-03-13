{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Egret.Rewrite.WellTyped
  ( -- * Types
   WellTypedRewrite
  ,At (..)
    -- * Constructing 'WellTypedRewrite's
  ,qequationToRewrite
    -- * Using 'WellTypedRewrite's
  ,rewriteHere
  ,allRewrites
  ,mkAtRewrite
  ,rewriteAt
  )
  where

import           Egret.Rewrite.Rewrite hiding (rewriteFail, options)
import qualified Egret.Rewrite.Rewrite as Rewrite
import           Egret.Rewrite.Expr
import           Egret.Rewrite.Equation

import           Egret.TypeChecker.Type
import           Egret.TypeChecker.Equation

import           Egret.Ppr

import           Control.Comonad.Store
import           Control.Lens.Plated

import           Data.Coerce

import Debug.Trace

newtype WellTypedRewrite tyenv = WellTypedRewrite (Rewrite (TypedExpr' tyenv) String)
  deriving (Semigroup, Monoid)

rewriteFail :: WellTypedRewrite tyenv
rewriteFail = WellTypedRewrite Rewrite.rewriteFail

options :: forall tyenv. [WellTypedRewrite tyenv] -> WellTypedRewrite tyenv
options xs =
  let xs' :: [Rewrite (TypedExpr' tyenv) String]
      xs' = coerce xs
  in
  coerce (Rewrite.options xs')

qequationToRewrite :: TypeEnv tyenv -> TypedQEquation String -> WellTypedRewrite tyenv
qequationToRewrite = undefined

rewriteHere :: WellTypedRewrite tyenv -> TypedExpr tyenv -> Maybe (TypedExpr tyenv)
rewriteHere (WellTypedRewrite re) = runRewrite re

allRewrites :: WellTypedRewrite tyenv -> TypedExpr tyenv -> [TypedExpr tyenv]
allRewrites re fa = 
  maybeCons (rewriteHere re fa)
    $ concatMap (experiment (allRewrites re)) (exprHoles fa)

mkAtRewrite :: At (WellTypedRewrite tyenv) -> WellTypedRewrite tyenv
mkAtRewrite = WellTypedRewrite . Rewrite . rewriteAt

rewriteAt :: At (WellTypedRewrite tyenv) -> TypedExpr tyenv -> Maybe (TypedExpr tyenv)
rewriteAt (At ix0 re) x =
    let res = allRewrites re x
    in
    traceShow (take 30 res) $ go ix0 res
  where
    go _ [] = Nothing
    go 0 (x:_) = Just x
    go ix (_:xs) = go (ix-1) xs

-- -- | Well-typed input ==> well-typed output
-- ensureWellTypedRewrite :: TypeEnv tyenv -> Rewrite Expr String -> WellTypedRewrite
-- ensureWellTypedRewrite env re = WellTypedRewrite . Rewrite $ \x ->
--   let r = runRewrite re x
--       b1 = not (isWellTyped env x)
--       b2 = or (fmap (isWellTyped env) r)
--   in
--   if b1 || b2
--     -- then trace ("well-typed implication: " ++ show (x, r)) r
--     then r
--     else Nothing
--     -- else trace ("not well-typed, " ++ show (b1,b2) ++ ": " ++ show (ppr x, fmap ppr r)) Nothing

toRewrite :: TypeEnv -> TypedDirectedQEquation -> WellTypedRewrite
toRewrite env (Dir Fwd eqn) = toFwdRewrite env eqn
toRewrite env (Dir Bwd eqn) = toFwdRewrite env (flipEqn eqn)

toFwdRewrite :: TypeEnv -> TypedQEquation -> WellTypedRewrite
toFwdRewrite env (lhs :=: rhs) = ensureWellTypedRewrite env $ Rewrite go
  where
    go e =
      case match lhs e of
        Left {} -> Nothing
        Right unifyEnv -> applyUnifyEnv unifyEnv rhs

-- | Precondition: 'UnifyEnv' is valid: Variable names occur
-- at most once in it.
applyTypedUnifyEnvEqn :: UnifyEnv String -> TypedQEquation -> Maybe (Equation Expr String)
applyTypedUnifyEnvEqn env (lhs :=: rhs) =
  liftA2 (:=:)
    (applyUnifyEnv env lhs) 
    (applyUnifyEnv env rhs)



maybeCons :: Maybe a -> [a] -> [a]
maybeCons Nothing xs = xs
maybeCons (Just x) xs = x : xs

