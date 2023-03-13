{-# LANGUAGE ScopedTypeVariables #-}

module Egret.TypeChecker.Equation
  (typeInferEquation
  ,TypedQEquation
  ,TypedDirectedQEquation
  -- ,toRewrite
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

typeInferEquation :: forall tyenv a. (Eq a, Show a) => TypeEnv' tyenv a -> Equation Expr a -> Either String (Type, Equation (TypedExpr' tyenv) a)
typeInferEquation env (lhs0 :=: rhs0) =
  go (lhs0 :=: rhs0) <|> fmap (fmap flipEqn) (go (rhs0 :=: lhs0))
  where
    go :: Equation Expr a -> Either String (Type, Equation (TypedExpr' tyenv) a)
    go (lhs :=: rhs) = do
      (ty, lhs') <- typeInfer env lhs
      (_, rhs') <- typeCheck env rhs ty
      pure (ty, lhs' :=: rhs')

typeInferQEquation :: forall tyenv. TypeEnv' tyenv (Var Int String) -> QEquation String -> Either String (Type, TypedQEquation tyenv)
typeInferQEquation env (lhs0 :=: rhs0) =
  go (lhs0 :=: rhs0) <|> fmap (fmap flipEqn) (go (rhs0 :=: lhs0))
  where
    -- go :: Equation Expr a -> Either String (Type, Equation (TypedExpr' tyenv) a)
    go (lhs :=: rhs) = do
      (ty, lhs') <- typeInferScoped env lhs
      (_, rhs') <- typeCheckScoped env rhs ty
      pure (ty, lhs' :=: rhs')

type TypedQEquation         tyenv = Equation         (TypedScopedExpr tyenv) String
type TypedDirectedQEquation tyenv = DirectedEquation (TypedScopedExpr tyenv) String

toTypedQEquation :: TypeEnv' tyenv (Var Int String) -> ParsedForall String -> Either String (TypedQEquation tyenv)
toTypedQEquation tcEnv =
  fmap snd . typeInferQEquation tcEnv . toQEquation

-- toQEquation :: Eq a => ParsedForall a -> QEquation a
-- toQEquation (ParsedForall boundVars (lhs :=: rhs)) =
--     abstract findVar lhs :=: abstract findVar rhs
--   where
--     findVar x = x `elemIndex` map unTyped boundVars

