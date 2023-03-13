{-# LANGUAGE ScopedTypeVariables #-}

module Egret.TypeChecker.Equation
  (typeInferEquation
  ,TypedQEquation
  ,TypedDirectedQEquation
  ,toRewrite
  )
  where

import           Egret.TypeChecker.Type
import           Egret.TypeChecker.Expr

import           Egret.Rewrite.Equation
import           Egret.Rewrite.Rewrite
import           Egret.Rewrite.Expr
-- import           Egret.Rewrite.WellTyped
import           Egret.Rewrite.Unify

import           Egret.Utils

import           Control.Applicative
import           Control.Monad

import           Bound.Scope
import           Bound

typeInferEquation :: TypeEnv tyenv -> Equation Expr String -> Either String (Type, Equation (TypedExpr' tyenv) String)
typeInferEquation env (lhs0 :=: rhs0) =
  go (lhs0 :=: rhs0) <|> go (rhs0 :=: lhs0)
  where
    go (lhs :=: rhs) =
      typeCheck env rhs =<< typeInfer env lhs

type TypedQEquation         tyenv = Equation         (TypedScopedExpr tyenv) String
type TypedDirectedQEquation tyenv = DirectedEquation (TypedScopedExpr tyenv) String
-- -- applyTypedUnifyEnv :: forall a. UnifyEnv a -> TypedScopedExpr a -> Maybe (Expr a)
-- -- applyTypedUnifyEnv env = joinedTraverseScope go
-- --   where
-- --     go (Typed ty i) =
-- --       case envLookup i env of
-- --         Just x -> undefined
--
