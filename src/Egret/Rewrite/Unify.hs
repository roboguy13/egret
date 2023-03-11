{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Egret.Rewrite.Unify
  (match
  ,applyUnifyEnv
  ,UnifyEnv
  ,UnifyError(..)
  )
  where

import           Bound

import           Egret.Rewrite.Expr

import           Control.Monad.State

newtype UnifyEnv a = UnifyEnv [(Int, Expr a)]
  deriving (Show, Semigroup, Monoid)

newtype UnifyError = UnifyError { getUnifyError :: String }
  deriving (Show)

type Unify a = StateT (UnifyEnv a) (Either UnifyError)

applyUnifyEnv :: Show a => UnifyEnv a -> ScopedExpr a -> Expr a
applyUnifyEnv env = instantiate go
  where
    go i =
      case envLookup i env of
        Just x -> x
        Nothing -> error $ "applyUnifyEnv: Cannot find " ++ show i ++ " in " ++ show env

match :: forall a. (Show a, Eq a) => ScopedExpr a -> Expr a -> Either UnifyError (UnifyEnv a)
match x0 y0 =
    flip execStateT mempty $ go (fromScope x0) y0
  where
    go :: Expr (Var Int a) -> Expr a -> Unify a ()
    go (V (B i)) rhs =
      gets (envLookup i) >>= \case
        Just e  -> tryMatch e rhs
        Nothing -> modify (envInsert i rhs)

    go (V (F x)) (V y) = tryMatch x y

    go (App x y) (App x' y') = do
      go x x'
      go y y'

    go e e' = cannotMatch e e'

unifyError :: String -> Unify x r
unifyError = lift . Left . UnifyError

cannotMatch :: (Show a, Show b) => a -> b -> Unify x r
cannotMatch x y =
  unifyError $ "Cannot match " ++ show x ++ " with " ++ show y

tryMatch :: (Eq a, Show a) => a -> a -> Unify x ()
tryMatch x y
  | x == y = pure ()
  | otherwise = cannotMatch x y

envLookup :: Int -> UnifyEnv a -> Maybe (Expr a)
envLookup i (UnifyEnv env) = lookup i env

envInsert :: Int -> Expr a -> UnifyEnv a -> UnifyEnv a
envInsert i e (UnifyEnv env) = UnifyEnv ((i, e) : env)

