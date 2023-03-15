{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

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

data Result m a
  = OutOfFuel (Fuel -> m (Result m a))
  | Success a
  | Failure Fuel
  deriving (Functor)

data TreeSearch m a b =
  TreeSearch
    { _splitSearch :: a -> [b]
    , _searchStep  :: b -> m (Iter a a)
    }

-- runLevel :: TreeSearch m a b -> a -> [m (Iter a a)]
-- runLevel = undefined

runSearch :: forall m a b. Monad m => TreeSearch m a b -> TreeSearchConfig -> a -> m (Result m a)
runSearch searcher config x0 = go x0 (_treeSearchFuel config)
  where
    splitSearch = _splitSearch searcher
    searchStep = _searchStep searcher

    fuelSplitter = _treeFuelSplitter config

    go :: b -> Fuel -> m (Result m a)
    go x (Fuel 0) = pure $ OutOfFuel (go x)
    go x fuel =
      searchStep x >>= \case
        Step y -> do
          let subtrees = splitSearch y
          case subtrees of
            [] -> pure $ Failure fuel
            (z:zs) -> do
              vs <- traverse (uncurry go) $ fuelSplitter (useFuel fuel) (z :| zs)
              foldr1M_NE (<++>) vs

        Done r -> pure $ Success r

type SearchCont m a = Fuel -> m (Result m a)

useFuel :: Fuel -> Fuel
useFuel (Fuel n) = Fuel (n-1)

(<+>) :: Monad m => SearchCont m a -> SearchCont m a -> SearchCont m a
f <+> g =
  f >=> \case
    OutOfFuel k -> pure $ OutOfFuel k
    Success x -> pure $ Success x
    Failure remainingFuel -> g remainingFuel

(<++>) :: Monad m => Result m a -> Result m a -> m (Result m a)
(<++>) (Success r) _ = pure $ Success r
(<++>) _ (Success r) = pure $ Success r
(<++>) (Failure fuel) (OutOfFuel k) = k fuel
(<++>) (OutOfFuel k) (Failure fuel) = k fuel
(<++>) (Failure fuel1) (Failure fuel2) = pure $ Failure (fuel1 <> fuel2)
(<++>) (OutOfFuel k1) (OutOfFuel k2) = pure $ OutOfFuel (k1 <+> k2)

-- instance Semigroup (Result m a) where
--   Success r <> _ = Success r
--   _ <> Success r = Success r
--
--   Failure fuel <> OutOfFuel k = k fuel
--   OutOfFuel k <> Failure fuel = k fuel
--
--   Failure fuel1 <> Failure fuel2 = Failure (fuel1 <> fuel2)
--
--   OutOfFuel k1 <> OutOfFuel k2 = OutOfFuel (k1 <+> k2)

-- | Get remaining unused fuel from failures
harvestFailures :: [Result m a] -> Fuel
harvestFailures = mconcat . mapMaybe getFailure

getOutOfFuel :: Result m a -> Maybe (Fuel -> m (Result m a))
getOutOfFuel (OutOfFuel k) = Just k
getOutOfFuel _ = Nothing

getSuccess :: Result m a -> Maybe a
getSuccess (Success x) = Just x
getSuccess _ = Nothing

getFailure :: Result m a -> Maybe Fuel
getFailure (Failure x) = Just x
getFailure _ = Nothing

