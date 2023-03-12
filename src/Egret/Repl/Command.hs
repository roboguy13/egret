module Egret.Repl.Command
  (Command (..)
  ,parseCommand
  )
  where

import           Egret.Tactic.Tactic

import           Egret.Parser.Utils
import           Egret.Parser.Tactic
import           Egret.Parser.Expr

import           Egret.Rewrite.Expr

import           Text.Megaparsec
import           Text.Megaparsec.Char

import           Data.Functor

data Command
  = RunBruteForce (Maybe Int) (Expr String)
  | RunTactic (Tactic String)
  | Undo
  deriving (Show)

parseCommand :: Parser Command
parseCommand =
  try parseUndo
    <|>
  try parseRunTactic
    <|>
  parseRunBruteForce

parseRunBruteForce :: Parser Command
parseRunBruteForce = label "brute_force usage" $ do
  keyword "brute_force"
  fuel <- (fmap read) <$> optional (some digitChar) :: Parser (Maybe Int)
  symbol ":"
  RunBruteForce fuel <$> parseExpr

parseUndo :: Parser Command
parseUndo = keyword "undo" $> Undo

parseRunTactic :: Parser Command
parseRunTactic = RunTactic <$> parseTactic

