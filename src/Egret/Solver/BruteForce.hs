{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}

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

import           Egret.Tactic.Tactic

import           Egret.TypeChecker.Type
import           Egret.TypeChecker.Equation

import           Egret.Proof.Trace

import           Egret.Solver.TreeSearch
import           Egret.Solver.Solver

import           Egret.Utils

import           Control.Monad.Writer

import           Data.List.NonEmpty (NonEmpty (..))
-- import qualified Data.List.NonEmpty as NonEmpty

import           Data.Semigroup
import           Data.Maybe

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

data BruteForceEnv tyenv a =
  BruteForceEnv
  { _bruteForceConfig :: BruteForceConfig
  , _bruteForceGoalRhs :: TypedExpr' tyenv a
  , _bruteForceEqnDb :: TypedEquationDB tyenv
  , _bruteForceTypeEnv :: TypeEnv tyenv
  , _bruteForceCurrentFuel :: Int
  }


bruteForce :: forall tyenv. TypeEnv tyenv -> BruteForceConfig -> TypedEquationDB tyenv -> Equation (TypedExpr' tyenv) String -> Either String (ProofTrace tyenv String)
bruteForce typeEnv config eqnDb (startLhs :=: goalRhs) =
  let
    startFuel = _bruteForceStartFuel config
    env = BruteForceEnv
          { _bruteForceConfig = config
          , _bruteForceGoalRhs = goalRhs
          , _bruteForceEqnDb = eqnDb
          , _bruteForceCurrentFuel = startFuel
          , _bruteForceTypeEnv = typeEnv
          }
  in
  undefined
  -- case runSubtree env (makeTree startLhs) of
  --   OutOfFuel _ -> Left $ "bruteForce: Ran out of fuel (started with " ++ show startFuel ++ " fuel)"
  --   Failure leftoverFuel -> Left $ "bruteForce: Failed with " ++ show leftoverFuel ++ " remaining fuel"
  --   Success x -> Right x
  where
    bruteForceSearcher :: SolverTreeSearch tyenv
    bruteForceSearcher =
      TreeSearch
        { _splitSearch = splitSearch
        , _searchStep = searchStep
        }

    splitSearch :: TypedExpr tyenv -> [TypedExpr tyenv]
    splitSearch =
      let tactics = concatMap (makeTactics . fst) eqnDb
      in
      catMaybes . traverse runTactic tactics

    searchStep :: TypedExpr tyenv -> TraceWriter tyenv String (Iter (TypedExpr tyenv) (TypedExpr tyenv))
    searchStep e =
      if e == goalRhs
        then pure $ Done e
        else undefined

    runTactic tactic = rewriteHere (unEither (tacticToRewrite typeEnv eqnDb tactic))

    unEither (Left x) = error $ "Internal error: makeTree: Could not find a rule name that should exit: " ++ show x
    unEither (Right y) = y

    updateTrace expr tactic = tell [ProofTraceStep expr tactic]

-- makeTree :: TypedExpr tyenv -> Result (TypedExpr tyenv)
-- makeTree expr0 = do
--   fuel <- asks _bruteForceCurrentFuel
--   goal <- asks _bruteForceGoalRhs
--   eqnDb <- asks _bruteForceEqnDb
--   typeEnv <- asks _bruteForceTypeEnv
--
--   pure $ go goal typeEnv eqnDb expr0 Nothing fuel
--   where
--     go goal typeEnv eqnDb expr tactic 0 = OutOfFuel (go goal typeEnv eqnDb expr tactic)
--     go goal typeEnv eqnDb expr tactic fuel
--       | expr == goal = Success (emptyTrace expr)
--       | otherwise =
--           case runTactic typeEnv eqnDb tactic expr of
--             Nothing -> Failure (fuel-1)
--             Just newExpr ->
--               let tactics = concatMap (makeTactics . fst) eqnDb
--                   fuels = branchFuels fuel (length eqnDb)
--                   results0 = zipWith (go goal typeEnv eqnDb newExpr) (map Just tactics) fuels
--                   results = map (updateTrace expr newExpr tactic) results0
--               in
--               sconcat (toNonEmpty results)
--
--     unEither (Left x) = error $ "Internal error: makeTree: Could not find a rule name that should exit: " ++ show x
--     unEither (Right y) = y
--
--     toNonEmpty [] = error "makeTree: Empty list of results"
--     toNonEmpty (x:xs) = x :| xs
--
--     runTactic _ _ Nothing = Just
--     runTactic typeEnv eqnDb (Just tactic) = rewriteHere (unEither (tacticToRewrite typeEnv eqnDb tactic))
--
--     updateTrace _ _ Nothing = id
--     updateTrace expr newExpr (Just tactic) = fmap (singletonTrace newExpr (ProofTraceStep expr tactic) <>)

makeTactics :: String -> [Tactic String]
makeTactics name =
  [ RewriteTactic Fwd name
  , RewriteTactic Bwd name
  ]

