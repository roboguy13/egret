{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Egret.Utils
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

splitCons :: (a -> b) -> ([a] -> [b]) -> NonEmpty a -> NonEmpty b
splitCons f g (x :| xs) = f x :| g xs

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

