{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Egret.Solver.Backtrack
  (BacktrackT
  ,Backtrack
  ,execBacktrack
  ,execBacktrackT
  ,toBacktrackT
  ,(<||>)
  )
  where

import           Control.Monad.Writer
import           Control.Monad.State
import           Control.Monad.Trans.Maybe

import           Control.Monad.Identity
import           Control.Monad.Except

import           Control.Applicative
import           Data.Foldable
import           Data.Functor

newtype BacktrackT e w m a =
  BacktrackT (ExceptT e (StateT w m) a)
  deriving (Functor, Applicative, Monad)

type Backtrack e w = BacktrackT e w Identity

instance MonadTrans (BacktrackT e w) where
  lift = BacktrackT . lift . lift

execBacktrack :: (Monoid w) => Backtrack e w a -> w
execBacktrack (BacktrackT act) = execState (runExceptT act) mempty

execBacktrackT :: (Monad m, Monoid w) => BacktrackT e w m a -> m w
execBacktrackT (BacktrackT act) = execStateT (runExceptT act) mempty

runBacktrackT :: BacktrackT e w m a -> w -> m (Either e a, w)
runBacktrackT (BacktrackT act) = runStateT (runExceptT act)

toBacktrackT :: (Monad m, Monoid w) => Writer w (Either e a) -> BacktrackT e w m a
toBacktrackT act =
  case runWriter act of
    (x, w) -> BacktrackT (put w) *> BacktrackT (ExceptT (pure x))

(<||>) :: (Monad m) => BacktrackT e w m a -> BacktrackT e w m a -> BacktrackT e w m a
x <||> y = do
    s <- BacktrackT get
    (a1, w1) <- lift $ runBacktrackT x s
    (a2, w2) <- lift $ runBacktrackT y s
    let xR = sequence (w1, a1)
        yR = sequence (w2, a2)

        z = xR <> yR
    traverse_ (BacktrackT . put . fst) z
    BacktrackT . ExceptT . pure $ fmap snd z

