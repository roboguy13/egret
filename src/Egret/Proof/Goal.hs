module Egret.Proof.Goal
  where

import           Egret.Rewrite.Expr
import           Egret.Rewrite.Equation

import           Egret.TypeChecker.Type

type Goal tyenv = TypedExpr tyenv

