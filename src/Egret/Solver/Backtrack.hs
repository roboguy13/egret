-- | This is like a "backtrack-able" Writer monad

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Egret.Solver.Backtrack
  (Backtrack
  ,execBacktrack
  ,runBacktrack
  ,putTell
  ,resetTo
  -- ,toBacktrack
  ,(<||>)
  ,current
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
  Backtrack (State w a)
  deriving (Functor, Applicative, Monad)

putTell :: Semigroup w => w -> Backtrack w ()
putTell x = Backtrack $ modify (<> x)

-- -- TODO: Does this instance completely make sense?
-- instance Monoid w => MonadWriter w (Backtrack w) where
--   writer (a, w) = putTell w $> a
--   listen act = do
--     w <- Backtrack get
--     fmap (,w) act
--   pass act = do
--     (x, f) <- act
--     Backtrack $ modify f
--     pure x

execBacktrack :: Monoid w => Backtrack w a -> w
execBacktrack (Backtrack act) = execState act mempty

runBacktrack :: Monoid w => Backtrack w a -> (a, w)
runBacktrack (Backtrack act) = runState act mempty

-- toBacktrack :: Writer w a -> Backtrack w a
-- toBacktrack act = do
--   s <- current
--   let (a, w) = runWriter act
--   Backtrack

(<||>) :: Monoid w => Backtrack w (Either e a) -> Backtrack w (Either e a) -> Backtrack w (Either e a)
x <||> y = do
    s <- current

    let (a1, w1) = runBacktrack (Backtrack (put s) *> x)
        (a2, w2) = runBacktrack (Backtrack (put s) *> y)
        xR = sequence (w1, a1)
        yR = sequence (w2, a2)

        z = xR <> yR

    traverse_ (Backtrack . put . fst) z
    Backtrack . pure $ fmap snd z

checkpoint :: (a -> Backtrack w b) -> Backtrack w (a -> Backtrack w b)
checkpoint k = do
  s <- Backtrack get
  pure $ \x -> Backtrack (put s) *> k x

current :: Backtrack w w
current = Backtrack get

resetTo :: w -> Backtrack w ()
resetTo = Backtrack . put

backtrackingChoice :: Monoid w => e -> [Backtrack w (Either e a)] -> Backtrack w (Either e a)
backtrackingChoice def [] = pure (Left def)
backtrackingChoice _ (x:xs) = foldr1_NE (<||>) (x :| xs)

