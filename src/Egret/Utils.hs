module Egret.Utils
  where

import           Bound

import           Control.Monad

joinedTraverseScope :: (Monad m, Traversable m, Applicative f) =>
     (t -> f (m a)) -> Scope t m a -> f (m a)
joinedTraverseScope f (Scope s) = join <$> traverse f' s
  where
    f' (B b) = f b
    f' (F a) = pure a


