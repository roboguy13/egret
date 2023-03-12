{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}

module Egret.Rewrite.Rewrite
  where

import           Control.Lens hiding (At)
import           Control.Lens.Plated

import           Data.Data.Lens
import           Data.Data

import           Control.Applicative

import           Control.Monad
import           Control.Comonad
import           Control.Comonad.Store

import           Control.Monad.Writer

import           Data.Monoid

import           Data.Maybe

import Debug.Trace

type Env f a = [(a, f a)]

newtype Rewrite f a =
  Rewrite { runRewrite :: f a -> Maybe (f a) }

instance Semigroup (Rewrite f a) where
  f <> g = Rewrite (runRewrite f >=> runRewrite g)

instance Monoid (Rewrite f a) where
  mempty = Rewrite Just

(<||>) :: Rewrite f a -> Rewrite f a -> Rewrite f a
f <||> g = Rewrite $ \x -> runRewrite f x <|> runRewrite g x

options :: [Rewrite f a] -> Rewrite f a
options = foldr (<||>) rewriteFail

rewriteFail :: Rewrite f a
rewriteFail = Rewrite (const Nothing)

data At a = At Int a
  deriving (Show, Functor)

mkAtRewrite :: (Show (f a), Plated (f a)) => At (Rewrite f a) -> Rewrite f a
mkAtRewrite = Rewrite . rewriteAt

rewriteHere :: Rewrite f a -> f a -> Maybe (f a)
rewriteHere = runRewrite

rewriteAt :: (Show (f a), Plated (f a)) => At (Rewrite f a) -> f a -> Maybe (f a)
rewriteAt (At ix0 re) x =
    let res = allRewrites re x
    in
    traceShow (take 30 res) $ go ix0 res
  where
    go _ [] = Nothing
    go 0 (x:_) = Just x
    go ix (_:xs) = go (ix-1) xs

rewriteThere :: Data (f a) => Rewrite f a -> (f a -> Bool) -> f a -> Maybe (f a)
rewriteThere re p =
  rewriteEverywhere go
  where
    go = Rewrite $ \x -> do
      guard (p x)
      runRewrite re x

rewriteEverywhere :: Data (f a) => Rewrite f a -> f a -> Maybe (f a)
rewriteEverywhere re fa =
  case runWriter $ rewriteMOf uniplate go fa of
    (r, Any True) -> Just r
    (_, Any False) -> Nothing
  where
    go x = do
      let y = runRewrite re x
      tell (Any (isJust y))
      pure y

rewriteEverywhere' :: Data (f a) => Rewrite f a -> f a -> f a
rewriteEverywhere' re fa = fromMaybe fa (rewriteEverywhere re fa)

allRewrites :: Plated (f a) => Rewrite f a -> f a -> [f a]
allRewrites re fa =
  maybeCons (rewriteHere re fa)
    $ concatMap (experiment (allRewrites re)) (holes fa)

maybeCons :: Maybe a -> [a] -> [a]
maybeCons Nothing xs = xs
maybeCons (Just x) xs = x : xs

