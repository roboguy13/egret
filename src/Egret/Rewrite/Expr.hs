-- {-# LANGUAGE PackageImports #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Egret.Rewrite.Expr
  -- (ExprCode
  -- )
  where

import           Data.String

import           Bound

import           Control.Monad
import           Control.Monad.Identity

import           Data.Functor.Compose

import           Egret.Ppr
import           Egret.Rewrite.Rewrite

import           Text.Show.Deriving

import           Data.Data
import           Control.Lens.Plated

data Expr a
  = V a
  | App (Expr a) (Expr a)
  deriving (Functor, Show, Eq, Ord, Foldable, Traversable, Data)

$(deriveShow1 ''Expr)

type ParsedExpr = Expr String
type ScopedExpr = Scope Int Expr

instance Plated (Expr a) where
  plate f (App x y) = App <$> f x <*> f y
  plate _ t = pure t

instance Applicative Expr where
  pure = V
  (<*>) = ap

instance Monad Expr where
  return = pure
  V x >>= f = f x
  App x y >>= f = App (x >>= f) (y >>= f)

instance Ppr a => Ppr (Expr a) where
  pprDoc (V x) = pprDoc x
  pprDoc (App f x) = sep [pprDoc f, pprArg x]
    where
      pprArg app@(App {}) = text "(" <> pprDoc app <> text ")"
      pprArg a = pprDoc a


-- import "ghc-lib-parser" GHC.Core
-- import "ghc-lib-parser" GHC.Parser
-- import "ghc-lib-parser" GHC.Parser.Lexer
-- import "ghc-lib-parser" GHC.Parser.PostProcess
-- import "ghc-lib-parser" GHC.Types.Id (Var)
-- import "ghc-lib-parser" GHC.Hs.Extension (GhcPs)
-- import "ghc-lib-parser" Language.Haskell.Syntax.Expr
--
-- newtype ExprCode = ExprCode String
--   deriving (IsString)
--
-- data Re a = a :=> a
--
-- -- | Uses _vars (HsUnboundVar) for universally quantified variable names
-- exprRewrite :: Re ExprCode -> Rewrite Expr Var
-- exprRewrite (lhs :=> rhs) =
--   case unP fullExpression (parserState lhs) of
--     POk _ lhsParsed ->
--       case unP fullExpression (parserState rhs) of
--         POk _ rhsParsed -> parsedExprRewrite (lhsParsed :=> rhsParsed)
--
-- parsedExprRewrite :: Re (LHsExpr GhcPs) -> Rewrite Expr Var
-- parsedExprRewrite (lhs :=> rhs) = undefined
--
-- parserState :: ExprCode -> PState
-- parserState = undefined
--
--
-- -- From https://hackage.haskell.org/package/ghc-parser-0.2.4.0/docs/src/Language.Haskell.GHC.HappyParser.html#fullExpression
-- fullExpression :: P (LHsExpr GhcPs)
-- fullExpression = parseExpression >>= \p -> runPV $ unECP p
--
