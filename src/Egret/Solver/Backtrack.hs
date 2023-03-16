-- | This is like a "backtrack-able" Writer monad

{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Egret.Solver.Backtrack
  (Backtrack
  ,execBacktrack
  ,runBacktrack
  ,toBacktrack
  ,(<||>)
  ,backtrackingChoice
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

import           Egret.Utils

newtype Backtrack w a =
  Backtrack (Writer w a)
  deriving (Functor, Applicative, Monad)

execBacktrack :: (Monoid w) => Backtrack w a -> w
execBacktrack (Backtrack act) = execWriter act

runBacktrack :: Backtrack w a -> (a, w)
runBacktrack (Backtrack act) = runWriter act

toBacktrack :: Writer w a -> Backtrack w a
toBacktrack = Backtrack

(<||>) :: (Monoid w) => Backtrack w (Either e a) -> Backtrack w (Either e a) -> Backtrack w (Either e a)
x <||> y = do
    (_, s) <- Backtrack $ listen $ pure ()

    let (a1, w1) = runBacktrack (toBacktrack (tell s) *> x)
        (a2, w2) = runBacktrack (toBacktrack (tell s) *> y)
        xR = sequence (w1, a1)
        yR = sequence (w2, a2)

        z = xR <> yR

    traverse_ (Backtrack . tell . fst) z
    Backtrack . pure $ fmap snd z

backtrackingChoice :: Monoid w => e -> [Backtrack w (Either e a)] -> Backtrack w (Either e a)
backtrackingChoice def [] = pure (Left def)
backtrackingChoice _ (x:xs) = foldr1_NE (<||>) (x :| xs)

