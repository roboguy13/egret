{-# LANGUAGE DeriveFunctor #-}

module Egret.Tactic.Tactic
  (Tactic (..)
  ,tacticName
  ,tacticToRewrite
  ,tacticToDirectedQEquation
  )
  where

import           Egret.Rewrite.Rewrite
import           Egret.Rewrite.Expr
import           Egret.Rewrite.Equation
import           Egret.Rewrite.Unify

import           Egret.Proof.Goal

import           Control.Applicative
import           Control.Monad

import           Data.Bifunctor

data Tactic a
  = RewriteTactic Direction a
  | UsingReplaceTactic a (Equation Expr String)
  deriving (Show, Functor)

tacticName :: Tactic a -> a
tacticName (RewriteTactic _ a) = a
tacticName (UsingReplaceTactic a _) = a

tacticToRewrite :: EquationDB String -> Tactic String -> Either String (Rewrite Expr String)
tacticToRewrite eqnDb tactic =
  toRewrite <$> tacticToDirectedQEquation eqnDb tactic

tacticToDirectedQEquation :: EquationDB String -> Tactic String -> Either String (DirectedQEquation String)
tacticToDirectedQEquation eqnDb (RewriteTactic dir name) =
  case lookup name eqnDb of
    Nothing -> Left $ "Cannot find equation named {" ++ name ++ "}"
    Just defn -> Right $ Dir dir $ toQEquation defn

tacticToDirectedQEquation eqnDb (UsingReplaceTactic name givenEqn) =
  case lookup name eqnDb of
    Nothing -> Left $ "Cannot find equation named {" ++ name ++ "}"
    Just defn ->
      case fwdUsingReplace defn givenEqn
             <|>
           bwdUsingReplace defn givenEqn
          of
        Nothing -> Left $ "Equation {" ++ name ++ "} does not apply"
        Just r -> Right r

bwdUsingReplace :: ParsedForall String -> Equation Expr String -> Maybe (DirectedQEquation String)
bwdUsingReplace def givenEqn =
  flipDirected <$> fwdUsingReplace def (flipEqn givenEqn)

fwdUsingReplace :: ParsedForall String -> Equation Expr String -> Maybe (DirectedQEquation String)
fwdUsingReplace defn givenEqn@(givenLhs :=: givenRhs) =
  case go of
    Left {} -> Nothing
    Right () -> Just $ Dir Fwd $ unquantified givenEqn
  where
    go = do
      let defnLhs :=: defnRhs = toQEquation defn

      unifyEnv <- first getUnifyError $ match defnLhs givenLhs 

      let subst'dDefRhs = applyUnifyEnv unifyEnv defnRhs

      when (subst'dDefRhs /= givenRhs)
        $ Left
          $ "Cannot match " ++ show subst'dDefRhs ++ " with " ++ show givenRhs

