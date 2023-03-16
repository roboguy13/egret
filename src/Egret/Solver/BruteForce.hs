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
import           Egret.Rewrite.Expr
import           Egret.Rewrite.WellTyped
import           Egret.Ppr

import           Egret.Tactic.Tactic

import           Egret.TypeChecker.Type
import           Egret.TypeChecker.Equation

import           Egret.Proof.Trace

import           Egret.Solver.TreeSearch
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
bruteForce typeEnv config eqnDb (startLhs :=: goalRhs) =
  let
    startFuel = Fuel $ _bruteForceStartFuel config
  in
  case runWriter $ runSearch
      bruteForceSearcher
      defaultTreeSearchConfig { _treeSearchFuel = startFuel }
      startLhs
      startFuel
    of
  (Success r, steps) -> Right $ ProofTrace goalRhs steps
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

    splitSearch :: TypedExpr tyenv -> [(TypedExpr tyenv, Tactic String)]
    splitSearch e =
      map (e,) allTactics

    searchStep :: (TypedExpr tyenv, Tactic String) -> TraceWriter tyenv String (Iter (Maybe (TypedExpr tyenv)) (TypedExpr tyenv))
    searchStep (e, tactic) =
      case trace ("running tactic " ++ show tactic) $ runTactic tactic e of
        Nothing -> pure $ Done Nothing
        Just e' ->
          if e' == goalRhs
            then pure $ Done $ Just e'
            else do
              pure $ Step e'

    runTactic tactic = rewriteHere (unEither (tacticToRewrite typeEnv eqnDb tactic))

    unEither (Left x) = error $ "Internal error: makeTree: Could not find a rule name that should exit: " ++ show x
    unEither (Right y) = y

    updateTrace expr tactic = tell [ProofTraceStep expr tactic]

makeTactics :: String -> [Tactic String]
makeTactics name =
  [ RewriteTactic Fwd name
  , RewriteTactic Bwd name
  ]

writerChoice :: MonadWriter w m => m a -> m a -> m a
writerChoice = undefined

