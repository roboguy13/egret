{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

module Egret.Solver.TreeSearch
  where

import           Egret.Utils
import           Egret.Ppr hiding ((<+>))

import           Egret.Solver.Backtrack

import           Data.Maybe
import           Data.List

import           Data.Proxy

import           Control.Monad.Reader

import           Data.Semigroup

import           Data.Foldable

import qualified Data.List.NonEmpty as NonEmpty
import           Data.List.NonEmpty (NonEmpty (..))

newtype Fuel = Fuel { getFuel :: Int }
  deriving (Show, Eq, Ord)

instance Semigroup Fuel where
  Fuel x <> Fuel y = Fuel (x + y)

instance Monoid Fuel where
  mempty = Fuel 0

instance Ppr Fuel where
  pprDoc (Fuel x) = text $ show x

-- | @length (_treeFuelSplitter fuel xs) = length xs@
--   @sum (map snd (_treeFuelSplitter fuel xs)) = fuel@
data TreeSearchConfig =
  TreeSearchConfig
  { _treeSearchFuel :: Fuel
  , _treeFuelSplitter :: forall a. Fuel -> [a] -> [(a, Fuel)]
  }

defaultTreeSearchConfig :: TreeSearchConfig
defaultTreeSearchConfig =
  TreeSearchConfig
  { _treeSearchFuel = Fuel 30000
  , _treeFuelSplitter = evenFuelSplitter
  }

-- if fuel `mod` length xs == 0
--   then (exists fuel'. map snd (evenFuelSplitter fuel xs) = replicate n fuel')
evenFuelSplitter :: Fuel -> [a] -> [(a, Fuel)]
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

-- data Result m a
--   = OutOfFuel (Fuel -> m (Result m a))
--   | Success a
--   | Failure Fuel
--   deriving (Functor)

data NotFound m a
  = OutOfFuel' (Fuel -> m (Result m a))
  | Failure' Fuel

type Result m a = Either (NotFound m a) a

pattern OutOfFuel k = Left (OutOfFuel' k)
pattern Failure x = Left (Failure' x)
pattern Success x = Right x

data TreeSearch m a b =
  TreeSearch
    { _splitSearch :: a -> [b]
    , _searchStep  :: b -> m (Iter (Maybe a) a)
    }

fanOut :: (Applicative f) =>
     (forall a. Fuel -> [a] -> [(a, Fuel)])
     -> (a -> Fuel -> f b) -> [a] -> Fuel -> [f b]
fanOut fuelSplitter f subtrees fuel = map (uncurry f) $ fuelSplitter (useFuel fuel) subtrees

runSearch :: forall m a b. Monad m => TreeSearch m a b -> TreeSearchConfig -> a -> Fuel -> m (Result m a)
runSearch searcher config x0 initialFuel =
    combineResults (Failure initialFuel)
      =<< sequence (go x0 initialFuel)
  where
    fuelSplitter = _treeFuelSplitter config
    splitSearch = _splitSearch searcher
    searchStep = _searchStep searcher

    go :: a -> Fuel -> [m (Result m a)]
    go x fuel =
      let
        subtrees = splitSearch x
      in
        fanOut fuelSplitter goStep subtrees fuel

    goStep :: b -> Fuel -> m (Result m a)
    goStep y (Fuel 0) = pure $ OutOfFuel (goStep y)
    goStep y fuel =
      searchStep y >>= \case
        Done (Just r) -> pure $ Success r
        Done Nothing -> pure $ Failure fuel
        Step z -> do
          xs <- sequence $ go z fuel
          combineResults (Failure fuel) xs

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

combineResults :: Monad m => Result m a -> [Result m a] -> m (Result m a)
combineResults z [] = pure z
combineResults z xs = foldr1M (<++>) xs

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

