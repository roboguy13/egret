{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}

module Egret.Tactic.Tactic
  (Tactic
  ,pattern RewriteTactic
  ,pattern UsingReplaceTactic
  ,pattern RewriteAtTactic

  ,tacticName
  ,tacticToRewrite
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

data BasicTactic a
  = RewriteTactic' Direction a
  | UsingReplaceTactic' a (Equation Expr String)
  deriving (Show, Functor)

data Tactic a
  = BasicTactic (BasicTactic a)
  | AtTactic (At (BasicTactic a))
  deriving (Show, Functor)

pattern RewriteTactic x y = BasicTactic (RewriteTactic' x y)
pattern UsingReplaceTactic x y = BasicTactic (UsingReplaceTactic' x y)
pattern RewriteAtTactic x y z = AtTactic (At x (RewriteTactic' y z))

basicTacticName :: BasicTactic a -> a
basicTacticName (RewriteTactic' _ a) = a
basicTacticName (UsingReplaceTactic' a _) = a

tacticName :: Tactic a -> a
tacticName (BasicTactic x) = basicTacticName x
tacticName (AtTactic (At _ x)) = basicTacticName x

tacticToRewrite :: EquationDB String -> Tactic String -> Either String (Rewrite Expr String)
tacticToRewrite eqnDb (AtTactic (At ix tactic)) =
  mkAtRewrite . At ix . toRewrite <$> basicTacticToDirectedQEquation eqnDb tactic
tacticToRewrite eqnDb (BasicTactic tactic) =
  toRewrite <$> basicTacticToDirectedQEquation eqnDb tactic

basicTacticToDirectedQEquation :: EquationDB String -> BasicTactic String -> Either String (DirectedQEquation String)
basicTacticToDirectedQEquation eqnDb (RewriteTactic' dir name) =
  case lookup name eqnDb of
    Nothing -> Left $ "Cannot find equation named {" ++ name ++ "}"
    Just defn -> Right $ Dir dir $ toQEquation defn

basicTacticToDirectedQEquation eqnDb (UsingReplaceTactic' name givenEqn) =
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

