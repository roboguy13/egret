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

import           Egret.Rewrite.Equation
import           Egret.Rewrite.WellTyped

import           Egret.Tactic.Tactic

import           Egret.TypeChecker.Type
import           Egret.TypeChecker.Equation

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

data BruteForceEnv tyenv a =
  BruteForceEnv
  { _bruteForceConfig :: BruteForceConfig
  , _bruteForceGoalRhs :: TypedExpr' tyenv a
  , _bruteForceEqnDb :: TypedEquationDB tyenv
  , _bruteForceTypeEnv :: TypeEnv tyenv
  , _bruteForceCurrentFuel :: Int
  }


bruteForce :: TypeEnv tyenv -> BruteForceConfig -> TypedEquationDB tyenv -> Equation (TypedExpr' tyenv) String -> Either String (ProofTrace tyenv String)
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
  case runSubtree env (makeTree startLhs) of
    OutOfFuel _ -> Left $ "bruteForce: Ran out of fuel (started with " ++ show startFuel ++ " fuel)"
    Failure leftoverFuel -> Left $ "bruteForce: Failed with " ++ show leftoverFuel ++ " remaining fuel"
    Success x -> Right x

data BruteForceResult' f a
  = OutOfFuel (f (BruteForceResult' f a))
  | Success a
  | Failure Int
  deriving (Functor)

type BruteForceResult tyenv f a = BruteForceResult' f (ProofTrace tyenv a)

-- | Keep track of fuel in current branch
newtype Subtree tyenv a = Subtree (Reader (BruteForceEnv tyenv String) a)
  deriving (Functor, Applicative, Monad, MonadReader (BruteForceEnv tyenv String))

makeTree :: TypedExpr tyenv -> Subtree tyenv (BranchResult tyenv String)
makeTree expr0 = do
  fuel <- asks _bruteForceCurrentFuel
  goal <- asks _bruteForceGoalRhs
  eqnDb <- asks _bruteForceEqnDb
  typeEnv <- asks _bruteForceTypeEnv

  pure $ go goal typeEnv eqnDb expr0 Nothing fuel
  where
    go goal typeEnv eqnDb expr tactic 0 = OutOfFuel (go goal typeEnv eqnDb expr tactic)
    go goal typeEnv eqnDb expr tactic fuel
      | expr == goal = Success (emptyTrace expr)
      | otherwise =
          case runTactic typeEnv eqnDb tactic expr of
            Nothing -> Failure (fuel-1)
            Just newExpr ->
              let tactics = concatMap (makeTactics . fst) eqnDb
                  fuels = branchFuels fuel (length eqnDb)
                  results0 = zipWith (go goal typeEnv eqnDb newExpr) (map Just tactics) fuels
                  results = map (updateTrace expr newExpr tactic) results0
              in
              sconcat (toNonEmpty results)

    unEither (Left x) = error $ "Internal error: makeTree: Could not find a rule name that should exit: " ++ show x
    unEither (Right y) = y

    toNonEmpty [] = error "makeTree: Empty list of results"
    toNonEmpty (x:xs) = x :| xs

    runTactic _ _ Nothing = Just
    runTactic typeEnv eqnDb (Just tactic) = rewriteHere (unEither (tacticToRewrite typeEnv eqnDb tactic))

    updateTrace _ _ Nothing = id
    updateTrace expr newExpr (Just tactic) = fmap (singletonTrace newExpr (ProofTraceStep expr tactic) <>)

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

(<+>) :: BranchContinuation tyenv a -> BranchContinuation tyenv a -> BranchContinuation tyenv a
f <+> g = \fuel ->
  case f fuel of
    OutOfFuel k -> OutOfFuel k
    Success x -> Success x
    Failure remainingFuel -> g remainingFuel

instance Semigroup (BranchResult tyenv a) where
  Success r <> _ = Success r
  _ <> Success r = Success r

  Failure fuel <> OutOfFuel k = k fuel
  OutOfFuel k <> Failure fuel = k fuel

  Failure fuel1 <> Failure fuel2 = Failure (fuel1 + fuel2)

  OutOfFuel k1 <> OutOfFuel k2 = OutOfFuel (k1 <+> k2)

-- | Yield when out of fuel so the branch can be resumed if another branch gives up early. The continuation contained in OutOfFuel has type @Int -> BranchResult a$
type BranchResult tyenv a = BruteForceResult tyenv ((->) Int) a

type BranchContinuation tyenv a = Int -> BranchResult tyenv a

-- | Run subtree until it succeeds, runs out of fuel or fails before running
-- out of fuel
runSubtree :: BruteForceEnv tyenv String -> Subtree tyenv a -> a
runSubtree env (Subtree m) = runReader m env

makeTactics :: String -> [Tactic String]
makeTactics name =
  [ RewriteTactic Fwd name
  , RewriteTactic Bwd name
  ]

