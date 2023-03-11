{-# LANGUAGE TemplateHaskell #-}

module Egret.Proof.Trace
  where

import           Egret.Rewrite.Expr
import           Egret.Rewrite.Equation

import           Egret.Tactic.Tactic

import           Egret.Proof.Goal

import           Control.Lens.TH

data ProofTraceStep a =
  ProofTraceStep
    { _stepGoal   :: Goal a
    , _stepTactic :: Tactic a
    }
  deriving (Show)

$(makeLenses ''ProofTraceStep)

data ProofTrace a =
  ProofTrace
    { _currentGoal :: Goal a
    , _traceSteps :: [ProofTraceStep a]
    }
  deriving (Show)

$(makeLenses ''ProofTrace)

emptyTrace :: Goal a -> ProofTrace a
emptyTrace goal = ProofTrace goal []

traceUndo :: ProofTrace a -> Either String (ProofTrace a)
traceUndo = go . _traceSteps
  where
    go [] = Left "At start, cannot undo"
    go (ProofTraceStep previous _ : xs) =
      Right $ ProofTrace previous xs

previousGoal :: ProofTrace a -> Maybe (Goal a)
previousGoal = go . _traceSteps
  where
    go [] = Nothing
    go (ProofTraceStep previous _ : _) = Just previous

applyToGoal :: Applicative f => Tactic a -> (Goal a -> f (Goal a)) -> ProofTrace a -> f (ProofTrace a)
applyToGoal tactic f (ProofTrace goal steps) =
  let newGoalM = f goal
      step = ProofTraceStep goal tactic
  in
  ProofTrace <$> newGoalM <*> pure (step : steps)

