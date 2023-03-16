{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Egret.Utils
  (joinedTraverseScope
  ,splitCons
  ,findFirst
  ,Iter (..)
  ,pattern Done
  ,pattern Step
  ,runIter
  ,NonEmpty (..)
  ,foldr1M_NE
  ,foldr1M
  ,foldr1_NE
  )
  where

import           Bound

import           Control.Monad

import           Data.Monoid

import           Data.List.NonEmpty (NonEmpty (..))

joinedTraverseScope :: (Monad m, Traversable m, Applicative f) =>
     (t -> f (m a)) -> Scope t m a -> f (m a)
joinedTraverseScope f (Scope s) = join <$> traverse f' s
  where
    f' (B b) = f b
    f' (F a) = pure a

splitCons :: (a -> b) -> ([a] -> [b]) -> [a] -> [b]
splitCons _ _ [] = []
splitCons f g (x : xs) = f x : g xs

findFirst :: (a -> Maybe b) -> [a] -> Maybe b
findFirst f = getFirst . foldMap (First . f)

-- | Early termination for @Done@ values
newtype Iter b a = Iter (Either b a)
  deriving (Functor, Applicative, Monad, Show)

pattern Done x = Iter (Left x)
pattern Step y = Iter (Right y)

runIter :: (a -> Iter b a) -> a -> b
runIter f initial =
  let Done r = go initial
  in r
  where
    go x = f x >>= go

foldr1M_NE :: forall m a. Monad m => (a -> a -> m a) -> NonEmpty a -> m a
foldr1M_NE f (x0 :| xs0) = go (x0 : xs0)
  where
    go :: [a] -> m a
    go [x] = pure x
    go (x : xs) = f x =<< go xs

foldr1M :: forall m a. Monad m => (a -> a -> m a) -> [a] -> m a
foldr1M _ [] = error "foldr1M: empty list"
foldr1M f (x0 : xs0) = go (x0 : xs0)
  where
    go :: [a] -> m a
    go [x] = pure x
    go (x : xs) = f x =<< go xs

foldr1_NE :: forall m a. (a -> a -> a) -> NonEmpty a -> a
foldr1_NE f (x :| xs) = foldr1 f (x : xs)

