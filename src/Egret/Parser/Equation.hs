module Egret.Parser.Equation
  (parseQuantified
  ,parseEquation
  ,parseEquationDef
  ,parseEquationDefs
  )
  where

import           Egret.Rewrite.Equation
import           Egret.Rewrite.Expr

import           Egret.Parser.Expr
import           Egret.Parser.Type

import           Egret.TypeChecker.Type

import           Egret.Parser.Utils

import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import           Data.Void

import           Control.Applicative hiding (many, some)

import           Data.Maybe

parseQuantified :: Parser (ParsedForall String)
parseQuantified = label "quantified equation" $ lexeme $ do
  forallVars <- fromMaybe [] <$> optional parseForallPart
  ParsedForall forallVars <$> parseEquation

parseForallPart :: Parser [Typed String]
parseForallPart = label "quantifier" $ lexeme $ do
  keyword "forall"
  xs <- some parseForallBinding
  symbol "."
  pure xs

parseForallBinding :: Parser (Typed String)
parseForallBinding = do
  symbol "("
  var <- parseIdentifier
  symbol "::"
  ty <- parseType
  symbol ")"
  pure (Typed ty var)

parseEquation :: Parser (Equation Expr String)
parseEquation = label "equation" $ lexeme $ do
  lhs <- parseExpr
  symbol "="
  rhs <- parseExpr
  pure (lhs :=: rhs)

parseEquationDef :: Parser (String, ParsedForall String)
parseEquationDef = label "equation definition" $ lexeme $ do
  name <- parseRuleName
  eqn <- parseQuantified
  pure (name, eqn)

parseEquationDefs :: Parser (EquationDB String)
parseEquationDefs = optional sc *> some parseEquationDef

