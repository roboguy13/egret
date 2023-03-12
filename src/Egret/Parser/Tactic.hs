module Egret.Parser.Tactic
  (parseTactic
  )
  where

import           Egret.Rewrite.Rewrite (At (..))
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
  try parseRewriteAt
    <|>
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

parseRewriteAt :: Parser (Tactic String)
parseRewriteAt = label "rewrite-at" $ lexeme $ do
  keyword "rewrite"
  keyword "at"
  ix <- label "number" $ lexeme $ read <$> some digitChar :: Parser Int
  dir <- fromMaybe Fwd <$> optional parseDirection
  RewriteAtTactic ix dir <$> parseRuleName

