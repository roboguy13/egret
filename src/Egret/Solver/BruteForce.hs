{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Egret.Solver.BruteForce
  (BruteForceConfig (..)
  ,defaultBruteForce
  ,bruteForce
  )
  where

import           Egret.Rewrite.Equation
import           Egret.Rewrite.WellTyped
import           Egret.Ppr

import           Egret.TypeChecker.Type
import           Egret.TypeChecker.Equation

import           Egret.Proof.Trace

import           Egret.Solver.TreeSearch
import           Egret.Solver.Backtrack
import           Egret.Solver.Solver

import           Egret.Utils

import           Control.Monad.Writer

import Debug.Trace

-- | We only keep track of the tree height since, if there
-- are a lot of rules (branches) most of them will immediately fail
newtype BruteForceConfig =
  BruteForceConfig
    { _bruteForceStartFuel :: Int
    }

defaultBruteForce :: BruteForceConfig
defaultBruteForce =
  BruteForceConfig
    { _bruteForceStartFuel  = 3000
    }

bruteForce :: forall tyenv. TypeEnv tyenv -> BruteForceConfig -> TypedEquationDB tyenv -> Equation (TypedExpr' tyenv) String -> Either String (ProofTrace tyenv String)
bruteForce tcEnv config eqnDb (startLhs :=: goalRhs) =
  let
    startFuel = Fuel $ _bruteForceStartFuel config
  in
  case runBacktrack $ runSearch
      bruteForceSearcher
      defaultTreeSearchConfig { _treeSearchFuel = startFuel }
      startLhs
      startFuel
    of
  (Success _, steps) -> traceShow (goalRhs, steps) $ Right $ ProofTrace goalRhs (toStepList steps)
  (OutOfFuel {}, _) -> Left $ "Ran out of fuel. Start with " <> ppr startFuel <> " fuel"
  (Failure fuelLeft, _) -> Left $ "Failed with " <> ppr fuelLeft <> " fuel remaining"
  where
    bruteForceSearcher :: SolverTreeSearch tyenv
    bruteForceSearcher =
      TreeSearch
        { _splitSearch = splitSearch
        , _searchStep = searchStep
        }

    rewriteDb = concatMap (makeRewrites tcEnv) eqnDb

    splitSearch :: TypedExpr tyenv -> [Rewritten tyenv]
    splitSearch e =
      concatMap (\(name, dir, re) -> zipWith (Rewritten e name dir) [0..] (allRewrites re e)) rewriteDb

    searchStep :: Rewritten tyenv -> Backtrack (TraceSteps tyenv String) (Iter (Maybe (TypedExpr tyenv)) (TypedExpr tyenv))
    searchStep rewritten = toBacktrack $ do
      let proofStep = rewrittenToStep rewritten
          result = rewrittenResult rewritten
      tell $ oneTraceStep proofStep
      if result == goalRhs
        then pure $ Done $ Just goalRhs
        else do
          pure $ Step result

makeRewrites :: TypeEnv tyenv -> (String, TypedQEquation tyenv) -> [(String, Direction, WellTypedRewrite tyenv)]
makeRewrites tcEnv (name, eqn) =
  [(name, Fwd, qequationToRewrite tcEnv (Dir Fwd eqn))
  ,(name, Bwd, qequationToRewrite tcEnv (Dir Bwd eqn))
  ]

