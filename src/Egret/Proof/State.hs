{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Egret.Proof.State
  (ProofEnv (..)
  ,ProofM (..)
  ,runProofM
  ,applyTacticM
  ,module Control.Monad.State
  ,module Control.Monad.Reader
  ,module Egret.Proof.Trace
  )
  where

import           Egret.Rewrite.Rewrite
import           Egret.Rewrite.Expr
import           Egret.Rewrite.Equation

import           Egret.Proof.Trace
import           Egret.Proof.Goal

import           Egret.TypeChecker.Type
import           Egret.TypeChecker.Equation

import           Egret.Tactic.Tactic

import           Control.Monad.State
import           Control.Monad.Reader
import           Data.Functor

data ProofEnv tyenv =
  ProofEnv
    { _proofEnvEqnDb :: TypedEquationDB tyenv
    , _proofEnvTypeEnv :: TypeEnv tyenv
    }

newtype ProofM tyenv a m r = ProofM (ReaderT (ProofEnv tyenv) (StateT (ProofTrace tyenv a) m) r)
  deriving (Functor, Applicative, Monad, MonadState (ProofTrace tyenv a), MonadReader (ProofEnv tyenv), MonadIO)

instance MonadTrans (ProofM tyenv a) where
  lift = ProofM . lift . lift

runProofM :: Monad m => TypeEnv tyenv -> TypedEquationDB tyenv -> Goal tyenv -> ProofM tyenv a m r -> m r
runProofM typeEnv eqnDb goal (ProofM m) = evalStateT (runReaderT m env) (emptyTrace goal) 
  where
    env = ProofEnv
      { _proofEnvEqnDb = eqnDb
      , _proofEnvTypeEnv = typeEnv
      }

applyTacticM :: Monad m => Tactic String -> ProofM tyenv String m (Maybe ())
applyTacticM tactic = do
  typeEnv <- asks _proofEnvTypeEnv
  (asks (tacticToRewrite typeEnv . _proofEnvEqnDb) <*> pure tactic) >>= \case
    Left {} -> pure Nothing
    Right re -> do
      tr <- get
      eqnDb <- asks _proofEnvEqnDb
      case applyToGoal typeEnv eqnDb tactic tr of
        Left {} -> pure Nothing
        Right newTr -> put newTr $> Just ()

