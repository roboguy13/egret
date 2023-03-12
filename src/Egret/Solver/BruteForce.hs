{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}

{-# OPTIONS_GHC -Wall #-}

module Egret.Solver.BruteForce
  (BruteForceConfig (..)
  ,defaultBruteForce
  ,bruteForce
  )
  where

import           Egret.Rewrite.Expr
import           Egret.Rewrite.Equation
import           Egret.Rewrite.Rewrite

import           Egret.Tactic.Tactic

import           Egret.Proof.Trace

import           Control.Monad.Reader

import           Data.List.NonEmpty (NonEmpty (..))
-- import qualified Data.List.NonEmpty as NonEmpty

import           Data.Semigroup

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

data BruteForceEnv a =
  BruteForceEnv
  { _bruteForceConfig :: BruteForceConfig
  , _bruteForceGoalRhs :: Expr a
  , _bruteForceEqnDb :: EquationDB a
  , _bruteForceCurrentFuel :: Int
  }


bruteForce :: BruteForceConfig -> EquationDB String -> Equation Expr String -> Either String (ProofTrace String)
bruteForce config eqnDb (startLhs :=: goalRhs) =
  let
    startFuel = _bruteForceStartFuel config
    env = BruteForceEnv
          { _bruteForceConfig = config
          , _bruteForceGoalRhs = goalRhs
          , _bruteForceEqnDb = eqnDb
          , _bruteForceCurrentFuel = startFuel
          }
  in
  case runSubtree env (makeTree startLhs) of
    OutOfFuel _ -> Left $ "bruteForce: Ran out of fuel (started with " ++ show startFuel ++ " fuel)"
    Failure leftoverFuel -> Left $ "bruteForce: Failed with " ++ show leftoverFuel ++ " remaining fuel"
    Success x -> Right x

data BruteForceResult' f a
  = OutOfFuel (f (BruteForceResult' f a))
  | Success a
  | Failure Int
  deriving (Functor)

type BruteForceResult f a = BruteForceResult' f (ProofTrace a)

-- | Keep track of fuel in current branch
newtype Subtree a = Subtree (Reader (BruteForceEnv String) a)
  deriving (Functor, Applicative, Monad, MonadReader (BruteForceEnv String))

makeTree :: Expr String -> Subtree (BranchResult String)
makeTree expr0 = do
  fuel <- asks _bruteForceCurrentFuel
  goal <- asks _bruteForceGoalRhs
  eqnDb <- asks _bruteForceEqnDb

  pure $ go goal eqnDb expr0 mempty fuel
  where
    go goal eqnDb expr re 0 = OutOfFuel (go goal eqnDb expr re)
    go goal eqnDb expr re fuel
      | expr == goal = Success (emptyTrace expr)
      | otherwise =
          case rewriteHere re expr of
            Nothing -> Failure (fuel-1)
            Just newExpr ->
              let tactics = concatMap (makeTactics . fst) eqnDb
                  rewrites = map (unEither . tacticToRewrite eqnDb) tactics
                  fuels = branchFuels fuel (length eqnDb)
                  results0 = zipWith (go goal eqnDb newExpr) rewrites fuels
                  results = map (fmap (singletonTrace undefined undefined <>)) results0
              in
              sconcat (toNonEmpty results)

    unEither (Left x) = error $ "Internal error: makeTree: Could not find a rule name that should exit: " ++ show x
    unEither (Right y) = y

    toNonEmpty [] = error "makeTree: Empty list of results"
    toNonEmpty (x:xs) = x :| xs

branchFuels :: Int -> Int -> [Int]
branchFuels totalFuel branchCount =
  let (fuelPerBranch, remaining) = totalFuel `divMod` branchCount
  in
  if fuelPerBranch == 0
    then replicate branchCount 0
    else
      if remaining > 0
      then remaining : replicate (branchCount-1) fuelPerBranch
      else replicate branchCount fuelPerBranch

(<+>) :: BranchContinuation a -> BranchContinuation a -> BranchContinuation a
f <+> g = \fuel ->
  case f fuel of
    OutOfFuel k -> OutOfFuel k
    Success x -> Success x
    Failure remainingFuel -> g remainingFuel

instance Semigroup (BranchResult a) where
  Success r <> _ = Success r
  _ <> Success r = Success r

  Failure fuel <> OutOfFuel k = k fuel
  OutOfFuel k <> Failure fuel = k fuel

  Failure fuel1 <> Failure fuel2 = Failure (fuel1 + fuel2)

  OutOfFuel k1 <> OutOfFuel k2 = OutOfFuel (k1 <+> k2)

-- | Yield when out of fuel so the branch can be resumed if another branch gives up early. The continuation contained in OutOfFuel has type @Int -> BranchResult a$
type BranchResult a = BruteForceResult ((->) Int) a

type BranchContinuation a = Int -> BranchResult a

-- | Run subtree until it succeeds, runs out of fuel or fails before running
-- out of fuel
runSubtree :: BruteForceEnv String -> Subtree a -> a
runSubtree env (Subtree m) = runReader m env

makeTactics :: String -> [Tactic String]
makeTactics name =
  [ RewriteTactic Fwd name
  , RewriteTactic Bwd name
  ]

