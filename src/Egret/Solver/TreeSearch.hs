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
import           Control.Monad.Writer

import           Data.Semigroup

import           Data.Foldable

import qualified Data.List.NonEmpty as NonEmpty
import           Data.List.NonEmpty (NonEmpty (..))

import Debug.Trace

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

data NotFound w a
  = OutOfFuel' (Fuel -> Backtrack w (Result w a))
  | Failure' Fuel

type Result m a = Either (NotFound m a) a

pattern OutOfFuel k = Left (OutOfFuel' k)
pattern Failure x = Left (Failure' x)
pattern Success x = Right x

data TreeSearch w a b =
  TreeSearch
    { _splitSearch :: a -> [b]
    , _searchStep  :: b -> Backtrack w (Iter (Maybe a) a)
    }

fanOut :: (Applicative f) =>
     (forall a. Fuel -> [a] -> [(a, Fuel)])
     -> (a -> Fuel -> f b) -> [a] -> Fuel -> [f b]
fanOut fuelSplitter f subtrees fuel = map (uncurry f) $ fuelSplitter (useFuel fuel) subtrees

runSearch :: forall w a b. Monoid w => TreeSearch w a b -> TreeSearchConfig -> a -> Fuel -> Backtrack w (Result w a)
runSearch searcher config x0 initialFuel =
    backtrackingChoice (Failure' initialFuel)
      $ go x0 initialFuel
  where
    fuelSplitter = _treeFuelSplitter config
    splitSearch = _splitSearch searcher
    searchStep = _searchStep searcher

    go :: a -> Fuel -> [Backtrack w (Result w a)]
    go x fuel =
      let
        subtrees = splitSearch x
      in
        fanOut fuelSplitter goStep subtrees fuel

    goStep :: b -> Fuel -> Backtrack w (Result w a)
    goStep y (Fuel 0) = do
      s <- current
      pure $ OutOfFuel (\fuel -> trace ("resuming with " <> ppr fuel <> " fuel") $ resetTo s *> goStep y fuel)
    goStep y fuel =
      searchStep y >>= \case
        Done (Just r) -> pure $ Success r
        Done Nothing  -> pure $ Failure fuel
        Step z        -> backtrackingChoice (Failure' fuel) $ go z fuel

type SearchCont w a = Fuel -> Backtrack w (Result w a)

useFuel :: Fuel -> Fuel
useFuel (Fuel n) = Fuel (n-1)

-- | Get remaining unused fuel from failures
harvestFailures :: [Result w a] -> Fuel
harvestFailures = mconcat . mapMaybe getFailure

getOutOfFuel :: Result w a -> Maybe (Fuel -> Backtrack w (Result w a))
getOutOfFuel (OutOfFuel k) = Just k
getOutOfFuel _ = Nothing

getSuccess :: Result w a -> Maybe a
getSuccess (Success x) = Just x
getSuccess _ = Nothing

getFailure :: Result w a -> Maybe Fuel
getFailure (Failure x) = Just x
getFailure _ = Nothing

