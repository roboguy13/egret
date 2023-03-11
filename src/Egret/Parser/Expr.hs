module Egret.Parser.Expr
  (parseExpr
  )
  where

import           Egret.Rewrite.Expr
import           Egret.Rewrite.Equation

import           Egret.Parser.Utils

import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import           Data.Void

import           Control.Applicative hiding (many, some)

parseExpr :: Parser ParsedExpr
parseExpr = lexeme $
  try parseApps
    <|>
  parseExpr'

parseExpr' :: Parser ParsedExpr
parseExpr' = lexeme $
  try (symbol "(" *> parseExpr <* symbol ")")
    <|>
  fmap V parseIdentifier

parseApps :: Parser ParsedExpr
parseApps = lexeme $ do
  f <- parseExpr'
  args <- some parseExpr'
  pure $ foldl1 App (f:args)

