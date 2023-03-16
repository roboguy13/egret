{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

{-# OPTIONS_GHC -Wall #-}

module Egret.Solver.BruteForce
  (BruteForceConfig (..)
  ,defaultBruteForce
  ,bruteForce
  )
  where

import           Egret.Rewrite.Equation
import           Egret.Rewrite.WellTyped
import           Egret.Ppr

import           Egret.Tactic.Tactic

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
  (Success _, steps) -> Right $ ProofTrace goalRhs steps
  (OutOfFuel {}, _) -> Left $ "Ran out of fuel. Start with " <> ppr startFuel <> " fuel"
  (Failure fuelLeft, _) -> Left $ "Failed with " <> ppr fuelLeft <> " fuel remaining"
  where
    bruteForceSearcher :: SolverTreeSearch tyenv
    bruteForceSearcher =
      TreeSearch
        { _splitSearch = splitSearch
        , _searchStep = searchStep
        }

    allTactics = concatMap (makeTactics . fst) eqnDb
    rewriteDb = concatMap (makeRewrites tcEnv) eqnDb

    -- splitSearch :: TypedExpr tyenv -> [(TypedExpr tyenv, (String, WellTypedRewrite tyenv))]
    splitSearch :: TypedExpr tyenv -> [Rewritten tyenv]
    splitSearch e =
      concatMap (\(name, dir, re) -> zipWith (Rewritten e name dir) [0..] (allRewrites re e)) rewriteDb

    searchStep :: Rewritten tyenv -> Backtrack [ProofTraceStep tyenv String] (Iter (Maybe (TypedExpr tyenv)) (TypedExpr tyenv))
    searchStep rewritten = toBacktrack $ do
      let proofStep = rewrittenToStep rewritten
          result = rewrittenResult rewritten
      -- case trace ("running step " ++ show step) $ runTactic tactic e of
      --   Nothing -> pure $ Done Nothing
      --   Just e' ->
      tell [proofStep]
      if result == goalRhs
        then pure $ Done $ Just goalRhs
        else do
          pure $ Step result

    runTactic tactic = rewriteHere (unEither (tacticToRewrite tcEnv eqnDb tactic))

    unEither (Left x) = error $ "Internal error: makeTree: Could not find a rule name that should exit: " ++ show x
    unEither (Right y) = y

    updateTrace expr tactic = tell [ProofTraceStep expr tactic]

makeTactics :: String -> [Tactic String]
makeTactics name =
  [ RewriteTactic Fwd name
  , RewriteTactic Bwd name
  ]

makeRewrites :: TypeEnv tyenv -> (String, TypedQEquation tyenv) -> [(String, Direction, WellTypedRewrite tyenv)]
makeRewrites tcEnv (name, eqn) =
  [(name, Fwd, qequationToRewrite tcEnv (Dir Fwd eqn))
  ,(name, Bwd, qequationToRewrite tcEnv (Dir Bwd eqn))
  ]

writerChoice :: MonadWriter w m => m a -> m a -> m a
writerChoice = undefined

