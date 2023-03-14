{-# LANGUAGE ScopedTypeVariables #-}

module Egret.TypeChecker.Equation
  (typeInferEquation
  ,typeInferQEquation
  ,TypedQEquation'
  ,TypedDirectedQEquation'
  ,TypedQEquation
  ,TypedDirectedQEquation
  ,TypedEquationDB
  ,typedUnquantified
  ,toTypedQEquation
  -- ,TypedForall
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
import           Egret.Ppr

import           Control.Applicative
import           Control.Monad

import           Bound.Scope
import           Bound

typeInferEquation :: forall tyenv a. (Eq a, Show a, Ppr a) => TypeEnv' tyenv a -> Equation Expr a -> Either String (Type, Equation (TypedExpr' tyenv) a)
typeInferEquation env (lhs0 :=: rhs0) =
  go (lhs0 :=: rhs0) <|> fmap (fmap flipEqn) (go (rhs0 :=: lhs0))
  where
    go :: Equation Expr a -> Either String (Type, Equation (TypedExpr' tyenv) a)
    go (lhs :=: rhs) = do
      (ty, _, lhs') <- typeInfer env lhs
      (_, _, rhs') <- typeCheck env rhs ty
      pure (ty, lhs' :=: rhs')

typeInferQEquation :: forall tyenv. TypeEnv' tyenv (Var Int String) -> QEquation String -> Either String (Type, TypedQEquation tyenv)
typeInferQEquation env (lhs0 :=: rhs0) =
  go (lhs0 :=: rhs0) <|> fmap (fmap flipEqn) (go (rhs0 :=: lhs0))
  where
    -- go :: Equation Expr a -> Either String (Type, Equation (TypedExpr' tyenv) a)
    go (lhs :=: rhs) = do
      (ty, _, lhs') <- typeInferScoped env lhs
      (_, _, rhs') <- typeCheckScoped env rhs ty
      pure (ty, lhs' :=: rhs')

type TypedQEquation'         tyenv = Equation         (TypedScopedExpr tyenv)
type TypedDirectedQEquation' tyenv = DirectedEquation (TypedScopedExpr tyenv) String
type TypedQEquation          tyenv = Equation         (TypedScopedExpr tyenv) String
type TypedDirectedQEquation  tyenv = DirectedEquation (TypedScopedExpr tyenv) String

type TypedEquationDB tyenv = [(String, TypedQEquation tyenv)]

-- type TypedForall tyenv = ParsedForall' (TypedQEquation' tyenv) Int

toTypedQEquation :: TypeEnv' tyenv (Var Int String) -> ParsedForall String -> Either String (TypedQEquation tyenv)
toTypedQEquation tcEnv =
  fmap snd . typeInferQEquation tcEnv . toQEquation

typedUnquantified :: Equation (TypedExpr' tyenv) a -> TypedQEquation' tyenv a
typedUnquantified (lhs :=: rhs) =
    go lhs :=: go rhs
  where
    go = abstractNothing

-- typeInferForall :: forall tyenv a. TypeEnv' tyenv (Var Int a) -> ParsedForall String -> Either String (TypedForall tyenv a)
-- typeInferForall tcEnv = undefined

-- toQEquation :: Eq a => ParsedForall a -> QEquation a
-- toQEquation (ParsedForall boundVars (lhs :=: rhs)) =
--     abstract findVar lhs :=: abstract findVar rhs
--   where
--     findVar x = x `elemIndex` map unTyped boundVars

