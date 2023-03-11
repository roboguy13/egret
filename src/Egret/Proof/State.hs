{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Egret.Proof.State
  (ProofM (..)
  ,runProofM
  ,applyTacticM
  ,module Control.Monad.State
  ,module Egret.Proof.Trace
  )
  where

import           Egret.Rewrite.Rewrite
import           Egret.Rewrite.Expr
import           Egret.Rewrite.Equation

import           Egret.Proof.Trace
import           Egret.Proof.Goal

import           Egret.Tactic.Tactic

import           Control.Monad.State
import           Control.Monad.Reader
import           Data.Functor

newtype ProofM a m r = ProofM (ReaderT (EquationDB a) (StateT (ProofTrace a) m) r)
  deriving (Functor, Applicative, Monad, MonadState (ProofTrace a), MonadReader (EquationDB a), MonadIO)

runProofM :: Monad m => EquationDB a -> Goal a -> ProofM a m r -> m r
runProofM eqnDb goal (ProofM m) = evalStateT (runReaderT m eqnDb) (emptyTrace goal) 

applyTacticM :: Monad m => Tactic String -> ProofM String m (Maybe ())
applyTacticM tactic = do
  (asks tacticToRewrite <*> pure tactic) >>= \case
    Left {} -> pure Nothing
    Right re -> applyRewriteM tactic re

-- | Tactic argument is for recording in trace
applyRewriteM :: Monad m => Tactic String -> Rewrite Expr String -> ProofM String m (Maybe ())
applyRewriteM tactic re = do
  tr <- get
  case applyToGoal tactic (rewriteHere re) tr of
    Just tr -> put tr $> Just ()
    Nothing -> pure Nothing

