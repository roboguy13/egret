{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

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

import           Control.Monad.State
import           Control.Monad.Reader
import           Control.Applicative

import           Data.Proxy

import           Data.Maybe
import           Data.List

-- | We only keep track of the tree height since, if there
-- are a lot of rules (branches) most of them will immediately fail
newtype BruteForceConfig =
  BruteForceConfig
    { _bruteForceHeight :: Int
    }

defaultBruteForce :: BruteForceConfig
defaultBruteForce =
  BruteForceConfig
    { _bruteForceHeight  = 3000
    }

data BruteForceEnv a =
  BruteForceEnv
  { _bruteForceConfig :: BruteForceConfig
  , _bruteForceGoalRhs :: Expr a
  , _bruteForceEqnDb :: EquationDB a
  }

bruteForce :: BruteForceConfig -> EquationDB String -> Equation Expr String -> Either String (ProofTrace String)
bruteForce config eqnDb (startLhs :=: goalRhs) =
    case runBranch env undefined height of
      (_, Success x) -> Right x
      (_, OutOfFuel Proxy) -> Left "Brute force: Ran out of fuel"
      (_, Failure fuel) -> Left $ "Brute force: Failed with " ++ show fuel ++ " fuel remaining"
  where
    env = undefined

    height = _bruteForceHeight config

    go env = do
      fueledTree <- generateFueledTree (emptyTrace startLhs)
      pure $ runFueledTree env fueledTree

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

generateFueledTree :: ProofTrace String -> Branch' [(Int, Branch String)]
generateFueledTree tr = do
  currentFuel <- get
  eqns <- asks _bruteForceEqnDb
  config <- asks _bruteForceConfig

  let tactics = concatMap (makeTactics . fst) eqns
  let fuels = branchFuels currentFuel (length tactics)

  pure (zipWith go tactics fuels)
  where
    go tactic fuel = (fuel, bruteForceBranch tactic tr)

-- | Run until a success, every branch fails or every branch rules out of
-- fuel
runFueledTree :: forall a. BruteForceEnv String -> [(Int, Branch a)] -> TreeResult a
runFueledTree env fueledBranches =
    let results = map (uncurry (flip (runBranch env))) fueledBranches
        remainingFuel = sum $ map fst results
    in
      undefined
    -- runBranchResults env (map snd results)

-- runBranchResults :: forall a. BruteForceEnv String -> [BranchResult a] -> TreeResult a
-- runBranchResults env results0 =
--     let remainingFuel = computeRemainingFuel results0
--     in
--     case findMaybe getSuccess results0 of
--       Just x -> Success x
--       Nothing -> runIter go (remainingFuel, mapMaybe getContinuation results0)
--   where
--     config = _bruteForceConfig env
--
--     go :: (Int, [BranchContinuation a]) -> Either (TreeResult a) (Int, [BranchContinuation a])
--     go (remainingFuel, ks) =
--       let refueled = refuelBranches config remainingFuel ks
--           newFuel = _
--       in
--       case findMaybe getSuccess refueled of
--         Just x -> Left $ Success x
--         Nothing -> go (newFuel, mapMaybe getContinuation refueled)
--
-- runIter :: (a -> Either b a) -> a -> b
-- runIter f z =
--     let Left r = go z
--     in
--     r
--   where
--     go x = f x >>= go

computeRemainingFuel :: [BranchResult a] -> Int
computeRemainingFuel = sum . mapMaybe getFailure

-- -- | When we have leftover fuel, choose a branch to give it to. Otherwise,
-- -- every branch has failed.
-- refuelBranch :: Int -> [BranchResult a] -> Maybe (BranchResult a)
-- refuelBranch _ [] = Nothing
-- refuelBranch fuel (OutOfFuel k : bs) =
--   Just $ k fuel

-- | Split leftover fuel among branches
refuelBranches :: BruteForceConfig -> Int -> [BranchContinuation a] -> [BranchResult a]
refuelBranches config fuel ks =
  let fuels = branchFuels fuel $ length ks
  in
  zipWith ($) ks fuels

-- | Keep track of fuel in current branch
newtype Branch' a = Branch (ReaderT (BruteForceEnv String) (State Int) a)
  deriving (Functor, Applicative, Monad, MonadState Int, MonadReader (BruteForceEnv String))

type Branch a = Branch' (BranchResult a)

-- | Only continue if we have fuel. Otherwise yield
runStep :: Branch a -> Branch a
runStep m = do
  fuel <- get
  env <- ask
  if fuel <= 0
    then pure (OutOfFuel (snd . runBranch env m)) -- Yield
    else m

data BruteForceResult f a
  = OutOfFuel (f (BruteForceResult f a))
  | Success (ProofTrace a)
  | Failure Int

-- | Yield when out of fuel so the branch can be resumed if another branch gives up early. The continuation contained in OutOfFuel has type @Int -> BranchResult a$
type BranchResult = BruteForceResult ((->) Int)

type BranchContinuation a = Int -> BranchResult a

-- | When the entire tree runs out of fuel, we are truly out of fuel
type TreeResult = BruteForceResult Proxy

forgetContinuation :: BruteForceResult f a -> BruteForceResult Proxy a
forgetContinuation (OutOfFuel {}) = OutOfFuel Proxy
forgetContinuation (Success x) = Success x
forgetContinuation (Failure fuel) = Failure fuel

fanOut :: [BranchContinuation a] -> BranchContinuation a
fanOut [] fuel = Failure fuel
fanOut xs0@(_:_) fuel =
  let fuels = branchFuels fuel (length xs0)
  in
  go (zip fuels xs0)
  where
    go [(fuel, k)] = k fuel
    go ((fuel, k):xs) =
      case k fuel of
        OutOfFuel k -> undefined

(<+>) :: BranchContinuation a -> BranchContinuation a -> BranchContinuation a
f <+> g = \fuel ->
  case f fuel of
    OutOfFuel k -> OutOfFuel k
    Success x -> Success x
    Failure remainingFuel -> g remainingFuel

combineContinuations :: [BranchContinuation a] -> BranchContinuation a
combineContinuations [] = Failure
combineContinuations (k:ks) = foldr1 (<+>) (k:ks)

-- | Run branch until it succeeds, runs out of fuel or fails before running
-- out of fuel
runBranch :: BruteForceEnv String -> Branch' a -> Int -> (Int, a)
runBranch env (Branch m) = swap . runState (runReaderT m env)
  where
    swap (a, b) = (b, a)

getContinuation :: BranchResult a -> Maybe (BranchContinuation a)
getContinuation (OutOfFuel k) = Just k
getContinuation _ = Nothing

getSuccess :: BranchResult a -> Maybe (ProofTrace a)
getSuccess (Success x) = Just x
getSuccess _ = Nothing

getFailure :: BranchResult a -> Maybe Int
getFailure (Failure leftoverFuel) = Just leftoverFuel
getFailure _ = Nothing

bruteForceBranch :: Tactic String -> ProofTrace String -> Branch String
bruteForceBranch tactic tr = do
  goalRhs <- asks _bruteForceGoalRhs  
  eqnDb <- asks _bruteForceEqnDb

  if _currentGoal tr == goalRhs
    then pure $ Success tr
    else
      runStep $
        case applyToGoal eqnDb tactic tr of
          Left err -> gets Failure
          Right tr2 -> do
            modify pred -- Subtract 1 from fuel

            config <- asks _bruteForceConfig
            currentFuel <- get

            let tactics = concatMap (makeTactics . fst) eqnDb
            let fuels = branchFuels currentFuel (length tactics)

            runWithFuels (zip fuels (map (`bruteForceBranch` tr2) tactics))

runWithFuels :: [(Int, Branch a)] -> Branch a
runWithFuels fueledBranches = do
    xs <- traverse go fueledBranches

    case findMaybe getSuccess xs of
      Just r -> pure $ Success r
      Nothing ->
        let failures = mapMaybe getFailure xs
            remainingFuel = sum failures
            continuation = combineContinuations (mapMaybe getContinuation xs)
        in
        pure $ continuation remainingFuel
  where
    go (fuel, branch) = do
      put fuel
      branch


makeTactics :: String -> [Tactic String]
makeTactics name =
  [ RewriteTactic Fwd name
  , RewriteTactic Bwd name
  ]

findMaybe :: (a -> Maybe b) -> [a] -> Maybe b
findMaybe f = listToMaybe . mapMaybe f

