{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}

module Egret.Proof.Trace
  where

import           Egret.Rewrite.Expr
import           Egret.Rewrite.Rewrite
import           Egret.Rewrite.Equation

import           Egret.Tactic.Tactic

import           Egret.Proof.Goal

import           Control.Lens.TH

import           Data.Maybe

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

instance Semigroup (ProofTrace a) where
  ProofTrace goal1 steps1 <> ProofTrace goal2 steps2 =
    ProofTrace goal2 (steps2 <> steps1)

singletonTrace :: Goal a -> ProofTraceStep a -> ProofTrace a
singletonTrace x y = ProofTrace x [y]

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

applyToGoal :: EquationDB String -> Tactic String -> ProofTrace String -> Either String (ProofTrace String)
applyToGoal eqnDb tactic (ProofTrace goal steps) = do
  re <- tacticToRewrite eqnDb tactic
  newGoal <- case rewriteHere re goal of
    Nothing -> Left "Rewrite tactic failed"
    Just x -> Right x

  let step = ProofTraceStep goal tactic
  Right $ ProofTrace newGoal (step : steps)

