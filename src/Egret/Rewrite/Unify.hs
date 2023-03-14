{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Egret.Rewrite.Unify
  (match
  ,UnifyEnv
  ,UnifyError(..)
  -- ,envLookup
  )
  where

import           Bound

import           Egret.Rewrite.Expr
import           Egret.TypeChecker.Type
import           Egret.TypeChecker.Expr

import           Egret.Utils

import           Control.Monad.State

type UnifyEnv tyenv = BoundSubst tyenv Int

-- newtype UnifyError = UnifyError { getUnifyError :: String }
--   deriving (Show)

type UnifyError = String

type Unify tyenv a = StateT (UnifyEnv tyenv a) (Either UnifyError)

match :: forall tyenv. TypeEnv tyenv -> TypedScopedExpr tyenv String -> TypedExpr tyenv -> Either UnifyError (UnifyEnv tyenv String)
match tyEnv x0 y0 =
    flip execStateT emptyBoundSubst $ go (fromTypedScope x0) y0
  where
    go :: TypedExpr' tyenv (Var Int String) -> TypedExpr' tyenv String -> Unify tyenv String ()
    go (TypedV (B i)) rhs =
      gets (boundSubstLookup i) >>= \case
        BoundSubstFound e  -> do
          let ty' = getType tyEnv e
          tryMatch e rhs
        BoundSubstNotFound k -> put (k rhs)

    go (TypedV (F x)) (TypedV y) = tryMatch x y

    go (TypedApp x y) (TypedApp x' y') = do
      go x x'
      go y y'

    go e e' = cannotMatch e e'

requireTypeEq :: Type -> Type -> Either UnifyError ()
requireTypeEq a b
  | a == b = pure ()
  | otherwise = Left $ "Unify: Cannot match type " ++ show a ++ " with type " ++ show b

requireTypeEqMaybe :: Type -> Type -> Maybe ()
requireTypeEqMaybe a b
  | a == b = pure ()
  | otherwise = Nothing

unifyError :: String -> Unify tyenv x r
unifyError = lift . Left

cannotMatch :: (Show a, Show b) => a -> b -> Unify tyenv x r
cannotMatch x y =
  unifyError $ "Cannot match " ++ show x ++ " with " ++ show y

tryMatch :: (Eq a, Show a) => a -> a -> Unify tyenv x ()
tryMatch x y
  | x == y = pure ()
  | otherwise = cannotMatch x y

