{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Egret.Solver.TreeSearch
  where

import           Egret.Utils

import           Data.Maybe
import           Data.List

import           Data.Proxy

import           Control.Monad.Reader

import           Data.Semigroup

import qualified Data.List.NonEmpty as NonEmpty
import           Data.List.NonEmpty (NonEmpty (..))

newtype Fuel = Fuel { getFuel :: Int }
  deriving (Show, Eq, Ord)

instance Semigroup Fuel where
  Fuel x <> Fuel y = Fuel (x + y)

instance Monoid Fuel where
  mempty = Fuel 0

-- | @length (_treeFuelSplitter fuel xs) = length xs@
--   @sum (map snd (_treeFuelSplitter fuel xs)) = fuel@
data TreeSearchConfig =
  TreeSearchConfig
  { _treeSearchFuel :: Fuel
  , _treeFuelSplitter :: forall a. Fuel -> NonEmpty a -> NonEmpty (a, Fuel)
  }

defaultTreeSearchConfig :: TreeSearchConfig
defaultTreeSearchConfig =
  TreeSearchConfig
  { _treeSearchFuel = Fuel 30000
  , _treeFuelSplitter = evenFuelSplitter
  }

-- if fuel `mod` length xs == 0
--   then (exists fuel'. map snd (evenFuelSplitter fuel xs) = replicate n fuel')
evenFuelSplitter :: Fuel -> NonEmpty a -> NonEmpty (a, Fuel)
evenFuelSplitter fuel xs =
  let (d, remainder) = getFuel fuel `divMod` length xs
  in
  if remainder == 0
    then fmap (,Fuel d) xs
    else
      splitCons
        (,Fuel remainder)
        (map (,Fuel d))
        xs

data Result a
  = OutOfFuel (Fuel -> Result a)
  | Success a
  | Failure Fuel
  deriving (Functor)

-- resume :: TreeSearchConfig -> Fuel -> [Result a] -> Iter (Result a) [Result a]
-- resume config fuel rs =
--     case findFirst getSuccess rs of
--       Just r -> Done $ Success r
--       Nothing ->
--         let splitter = _treeFuelSplitter config
--             ks = mapMaybe getOutOfFuel rs
--         in
--         case harvestFailures rs of
--           Fuel 0 ->
--             if not (null ks)
--               then Done $ let r = OutOfFuel (const r) in r
--               else Done . Failure $ Fuel 0
--
--           _ -> Step . map (uncurry ($)) $ splitter fuel ks

-- data TreeSearchStrategy

class TreeSearch a where
  splitSearch :: a -> NonEmpty a
  searchStep :: a -> Iter (Result a) a
  -- runTree :: Result a -> 
  -- -- searchBranch :: a -> Result a
  -- spawnBranches :: TreeSearchConfig -> a -> Iter (Result a) [Result a]
  -- combineBranches :: TreeSearchConfig -> [Result a] -> Result a

runSearch :: TreeSearch a => TreeSearchConfig -> a -> Result a
runSearch config x0 = go x0 (_treeSearchFuel config)
  where
    fuelSplitter = _treeFuelSplitter config

    go x (Fuel 0) = OutOfFuel (go x)
    go x fuel =
      case searchStep x of
        Step y ->
          let subtrees = splitSearch y
          in
          sconcat $ uncurry go <$> fuelSplitter fuel subtrees

        Done (Success r) -> Success r
        Done (Failure subFuel) -> Failure $ subFuel <> fuel
        Done (OutOfFuel k) -> k fuel -- TODO: Does this make sense?

type SearchCont a = Fuel -> Result a

(<+>) :: SearchCont a -> SearchCont a -> SearchCont a
f <+> g = \fuel ->
  case f fuel of
    OutOfFuel k -> OutOfFuel k
    Success x -> Success x
    Failure remainingFuel -> g remainingFuel

instance Semigroup (Result a) where
  Success r <> _ = Success r
  _ <> Success r = Success r

  Failure fuel <> OutOfFuel k = k fuel
  OutOfFuel k <> Failure fuel = k fuel

  Failure fuel1 <> Failure fuel2 = Failure (fuel1 <> fuel2)

  OutOfFuel k1 <> OutOfFuel k2 = OutOfFuel (k1 <+> k2)

-- searchStep :: Branch

-- runTreeSearch :: forall a. TreeSearch a => TreeSearchConfig -> a -> Result a
-- runTreeSearch config = undefined --go
--   where
--     go :: a -> Iter (Result a) (Result a)
--     go x = do
--       results <- spawnBranches config x
--       let fuel = harvestFailures results
--       xs <- resume config fuel results
--       undefined
--       -- mapM_ go xs

-- | Get remaining unused fuel from failures
harvestFailures :: [Result a] -> Fuel
harvestFailures = mconcat . mapMaybe getFailure

getOutOfFuel :: Result a -> Maybe (Fuel -> Result a)
getOutOfFuel (OutOfFuel k) = Just k
getOutOfFuel _ = Nothing

getSuccess :: Result a -> Maybe a
getSuccess (Success x) = Just x
getSuccess _ = Nothing

getFailure :: Result a -> Maybe Fuel
getFailure (Failure x) = Just x
getFailure _ = Nothing

