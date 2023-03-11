module Egret.Parser.Tactic
  (parseTactic
  )
  where

import           Egret.Rewrite.Expr
import           Egret.Rewrite.Equation
import           Egret.Tactic.Tactic

import           Egret.Parser.Utils
import           Egret.Parser.Equation

import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import           Data.Functor
import           Data.Maybe

parseTactic :: Parser (Tactic String)
parseTactic =
  try parseRewrite
    <|>
  parseUsingReplace

parseRewrite :: Parser (Tactic String)
parseRewrite = label "rewrite tactic" $ lexeme $ do
  keyword "rewrite"
  dir <- fromMaybe Fwd <$> optional parseDirection
  RewriteTactic dir <$> parseRuleName

parseUsingReplace :: Parser (Tactic String)
parseUsingReplace = label "using-replace tactic" $ lexeme $ do
  keyword "using"
  ruleName <- parseRuleName
  keyword "replace"
  UsingReplaceTactic ruleName <$> parseEquation

parseDirection :: Parser Direction
parseDirection = label "direction" $ lexeme $
  (symbol "->" $> Fwd)
    <|>
  (symbol "<-" $> Bwd)

