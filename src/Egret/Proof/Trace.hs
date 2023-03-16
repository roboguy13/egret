{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}

module Egret.Proof.Trace
  where

import           Egret.Rewrite.Expr
import           Egret.Rewrite.Rewrite
import           Egret.Rewrite.WellTyped
import           Egret.Rewrite.Equation

import           Egret.Tactic.Tactic

import           Egret.TypeChecker.Type
import           Egret.TypeChecker.Equation

import           Egret.Proof.Goal

import           Egret.Ppr

import           Control.Lens.TH

import           Data.Maybe

import           Control.Monad.Writer

data ProofTraceStep tyenv a =
  ProofTraceStep
    { _stepGoal   :: Goal tyenv
    , _stepTactic :: Tactic a
    }
  deriving (Show)

$(makeLenses ''ProofTraceStep)

data ProofTrace tyenv a =
  ProofTrace
    { _currentGoal :: Goal tyenv
    , _traceSteps :: [ProofTraceStep tyenv a]
    }
  deriving (Show)

$(makeLenses ''ProofTrace)

instance Semigroup (ProofTrace tyenv a) where
  ProofTrace goal1 steps1 <> ProofTrace goal2 steps2 =
    ProofTrace goal2 (steps2 <> steps1)

instance Ppr a => Ppr (ProofTraceStep tyenv a) where
  pprDoc (ProofTraceStep e tactic) =
    text (ppr e)
      $$ (text " ={" <> pprDoc (tacticName tactic) <> text "}")

instance Ppr a => Ppr (ProofTrace tyenv a) where
  pprDoc (ProofTrace goal steps0) =
    let steps = reverse steps0
    in
    vcat (map pprDoc steps)
      $$
    pprDoc goal

-- type TraceWriter tyenv a = Writer [ProofTraceStep tyenv a]

newtype TraceSteps tyenv a = TraceSteps [ProofTraceStep tyenv a]
  deriving (Show)

instance Semigroup (TraceSteps tyenv a) where
  TraceSteps xs <> TraceSteps ys = TraceSteps (ys <> xs)

instance Monoid (TraceSteps tyenv a) where
  mempty = TraceSteps []

oneTraceStep :: ProofTraceStep tyenv a -> TraceSteps tyenv a
oneTraceStep = TraceSteps . (:[])

toStepList :: TraceSteps tyenv a -> [ProofTraceStep tyenv a]
toStepList (TraceSteps xs) = xs

singletonTrace :: Goal tyenv -> ProofTraceStep tyenv a -> ProofTrace tyenv a
singletonTrace x y = ProofTrace x [y]

emptyTrace :: Goal tyenv -> ProofTrace tyenv a
emptyTrace goal = ProofTrace goal []

traceUndo :: ProofTrace tyenv a -> Either String (ProofTrace tyenv a)
traceUndo = go . _traceSteps
  where
    go [] = Left "At start, cannot undo"
    go (ProofTraceStep previous _ : xs) =
      Right $ ProofTrace previous xs

previousGoal :: ProofTrace tyenv a -> Maybe (Goal tyenv)
previousGoal = go . _traceSteps
  where
    go [] = Nothing
    go (ProofTraceStep previous _ : _) = Just previous

applyToGoal :: TypeEnv tyenv -> TypedEquationDB tyenv -> Tactic String -> ProofTrace tyenv String -> Either String (ProofTrace tyenv String)
applyToGoal typeEnv eqnDb tactic (ProofTrace goal steps) = do
  re <- tacticToRewrite typeEnv eqnDb tactic
  newGoal <- case rewriteHere re goal of
    Nothing -> Left "Rewrite tactic failed"
    Just x -> Right x

  let step = ProofTraceStep goal tactic
  Right $ ProofTrace newGoal (step : steps)

