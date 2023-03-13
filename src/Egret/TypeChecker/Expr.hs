module Egret.TypeChecker.Expr
  where

import           Egret.Rewrite.Expr
import           Egret.TypeChecker.Type

import           Bound

-- type TypedExpr = Expr Name
--
-- untypeExpr :: TypedExpr -> Expr String
-- untypeExpr = fmap go
--   where
--     go (Typed _ x) = x
--
