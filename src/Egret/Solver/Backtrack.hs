{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Egret.Solver.Backtrack
  -- (Backtrack
  -- ,execBacktrack
  -- ,toBacktrack
  -- ,(<||>)
  -- )
  where

import           Control.Monad.Writer
import           Control.Monad.State
import           Control.Monad.Trans.Maybe

import           Control.Applicative
import           Data.Foldable
import           Data.Functor

newtype Backtrack w a =
  Backtrack (MaybeT (State w) a)
  deriving (Functor, Applicative, Monad, MonadState w)

execBacktrack :: Monoid w => Backtrack w a -> w
execBacktrack (Backtrack act) = execState (runMaybeT act) mempty

runBacktrack :: Backtrack w a -> w -> (Maybe a, w)
runBacktrack (Backtrack act) = runState (runMaybeT act)

toBacktrack :: Monoid w => Writer w (Maybe a) -> Backtrack w a
toBacktrack act =
  case runWriter act of
    (x, w) -> put w *> Backtrack (MaybeT (pure x))

instance Alternative (Backtrack w) where
  empty = Backtrack . MaybeT $ pure Nothing
  x <|> y = do
    s <- get
    case (runBacktrack x s, runBacktrack y s) of
      ((a1, w1), (a2, w2)) -> do
        let xR = sequence (w1, a1)
            yR = sequence (w2, a2)

            z = xR <|> yR
        traverse_ (put . fst) z
        Backtrack . MaybeT . pure $ fmap snd z

