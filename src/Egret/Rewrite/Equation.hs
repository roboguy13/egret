{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}

module Egret.Rewrite.Equation
  (Equation (..)
  ,equationLhs
  ,equationRhs
  ,flipEqn
  ,EquationDB (..)
  ,ParsedForall' (..)
  ,ParsedForall (..)
  ,forallQuantifiedVars
  ,forallQuantifiedVarsDeBruijn
  ,QEquation (..)
  ,DirectedQEquation (..)
  ,Direction (..)
  ,Directed (..)
  ,DirectedEquation (..)
  ,flipDirection
  ,flipDirected
  ,toQEquation
  ,unquantified
  -- ,applyUnifyEnvEqn
  -- ,specifyQEquation
  -- ,untypedToRewrite
  )
  where

import           Bound

import           Data.Functor
import           Control.Monad.Identity

import           Data.Monoid
import           Data.List

import           Egret.Rewrite.Expr
import           Egret.Rewrite.Rewrite
import           Egret.Rewrite.Unify
import           Egret.TypeChecker.Type

data Equation f a = f a :=: f a
  deriving (Functor, Show)

equationLhs, equationRhs :: Equation f a -> f a
equationLhs (lhs :=: _) = lhs
equationRhs (_ :=: rhs) = rhs

flipEqn :: Equation f a -> Equation f a
flipEqn (lhs :=: rhs) = rhs :=: lhs

data ParsedForall' f a b =
  ParsedForall [a] (f b)
  deriving (Functor, Show)

type ParsedForall a = ParsedForall' (Equation Expr) (Typed a) a

forallQuantifiedVars :: ParsedForall' f a b -> [a]
forallQuantifiedVars (ParsedForall xs _) = xs

-- | TODO: Find a nicer design than using this
forallQuantifiedVarsDeBruijn :: ParsedForall' f (Typed a) b -> [Typed Int]
forallQuantifiedVarsDeBruijn (ParsedForall xs _) = zipWith go xs [0..]
  where
    go (Typed ty _) = Typed ty

type EquationDB a = [(String, ParsedForall a)]


data Direction = Fwd | Bwd
  deriving (Show, Eq, Ord)

data Directed a = Dir Direction a
  deriving (Show, Functor)

type DirectedEquation f a = Directed (Equation f a)

flipDirection :: Direction -> Direction
flipDirection Fwd = Bwd
flipDirection Bwd = Fwd

flipDirected :: DirectedEquation f a -> DirectedEquation f a
flipDirected (Dir dir eqn) = Dir (flipDirection dir) eqn

-- | Quantified Equation using Bound (de Bruijn indices)
type QEquation           = Equation         ScopedExpr
type DirectedQEquation a = DirectedEquation ScopedExpr a

unquantified :: Equation Expr a -> QEquation a
unquantified (lhs :=: rhs) =
    go lhs :=: go rhs
  where
    go = abstract (const Nothing)

toQEquation :: Eq a => ParsedForall a -> QEquation a
toQEquation (ParsedForall boundVars (lhs :=: rhs)) =
    abstract findVar lhs :=: abstract findVar rhs
  where
    findVar x = x `elemIndex` map unTyped boundVars

-- applyUnifyEnvEqn :: (Show a, Eq a) => UnifyEnv a -> QEquation a -> Equation Expr a
-- applyUnifyEnvEqn env (lhs :=: rhs) =
--   applyUnifyEnv env lhs :=: applyUnifyEnv env rhs
--
-- -- | The resulting QEquation should not have any bound variables
-- specifyQEquation :: (Eq a, Show a) => QEquation a -> Expr a -> Either UnifyError (QEquation a)
-- specifyQEquation (lhs :=: rhs) e = do
--   subst <- match lhs e
--
--   let doSubst = applyUnifyEnv subst 
--
--   pure (unquantified (doSubst lhs :=: doSubst rhs))

-- untypedToRewrite :: (Show a, Eq a) => DirectedQEquation a -> Rewrite Expr a
-- untypedToRewrite (Dir Fwd eqn) = toFwdRewrite eqn
-- untypedToRewrite (Dir Bwd eqn) = toFwdRewrite (flipEqn eqn)
--
-- toFwdRewrite :: forall a. (Show a, Eq a) => QEquation a -> Rewrite Expr a
-- toFwdRewrite (lhs :=: rhs) = Rewrite go
--   where
--     go :: Expr a -> Maybe (Expr a)
--     go e =
--       case match lhs e of
--         Left {} -> Nothing
--         Right env -> Just $ applyUnifyEnv env rhs
--
