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
import           Egret.Rewrite.WellTyped
import           Egret.Rewrite.Expr
import           Egret.Rewrite.Equation
import           Egret.Rewrite.Unify

import           Egret.TypeChecker.Type
import           Egret.TypeChecker.Equation

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

tacticToRewrite :: TypeEnv tyenv -> TypedEquationDB tyenv -> Tactic String -> Either String (WellTypedRewrite tyenv)
tacticToRewrite tcEnv eqnDb (AtTactic (At ix tactic)) =
  mkAtRewrite . At ix . qequationToRewrite tcEnv <$> basicTacticToDirectedQEquation tcEnv eqnDb tactic

tacticToRewrite tcEnv eqnDb (BasicTactic tactic) =
  qequationToRewrite tcEnv <$> basicTacticToDirectedQEquation tcEnv eqnDb tactic

basicTacticToDirectedQEquation :: TypeEnv tyenv -> TypedEquationDB tyenv -> BasicTactic String -> Either String (TypedDirectedQEquation tyenv)
basicTacticToDirectedQEquation tcEnv eqnDb (RewriteTactic' dir name) =
  case lookup name eqnDb of
    Nothing -> Left $ "Cannot find equation named {" ++ name ++ "}"
    Just defn -> Right $ Dir dir defn

basicTacticToDirectedQEquation tcEnv eqnDb (UsingReplaceTactic' name givenEqn) =
  case lookup name eqnDb of
    Nothing -> Left $ "Cannot find equation named {" ++ name ++ "}"
    Just defn -> do
      (_, typedGivenEqn) <- typeInferEquation tcEnv givenEqn
      case fwdUsingReplace tcEnv defn typedGivenEqn
             <|>
           bwdUsingReplace tcEnv defn typedGivenEqn
          of
        Nothing -> Left $ "Equation {" ++ name ++ "} does not apply"
        Just r -> Right r

bwdUsingReplace :: TypeEnv tyenv -> TypedQEquation tyenv -> Equation (TypedExpr' tyenv) String -> Maybe (TypedDirectedQEquation tyenv)
bwdUsingReplace tcEnv def givenEqn =
  flipDirected <$> fwdUsingReplace tcEnv def (flipEqn givenEqn)

fwdUsingReplace :: TypeEnv tyenv -> TypedQEquation tyenv -> Equation (TypedExpr' tyenv) String -> Maybe (TypedDirectedQEquation tyenv)
fwdUsingReplace tcEnv defn givenEqn@(givenLhs :=: givenRhs) =
  case go of
    Left {} -> Nothing
    Right () -> Just $ Dir Fwd $ typedUnquantified givenEqn
  where
    go = do
      let defnLhs :=: defnRhs = defn

      unifyEnv <- first getUnifyError $ match tcEnv defnLhs givenLhs 

      let subst'dDefRhs = applyBoundSubst unifyEnv defnRhs

      when (subst'dDefRhs /= givenRhs)
        $ Left
          $ "Cannot match " ++ show subst'dDefRhs ++ " with " ++ show givenRhs

