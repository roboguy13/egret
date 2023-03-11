module Egret.Parser.Utils
  where

import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import           Data.Void

import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Set as Set

import           Control.Applicative hiding (some, many)

import           System.IO
import           System.Exit

type Parser = Parsec Void String

sc :: Parser ()
sc = L.space
  space1
  (L.skipLineComment "--")
  (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

keyword :: String -> Parser String
keyword str = lexeme (string str <* notFollowedBy alphaNumChar)

parse' :: Parser a -> String -> Either String a
parse' p str =
  case parse p "<input>" str of
    Left err -> Left $ errorBundlePretty err
    Right x -> Right x

requiredParseIO :: String -> Parser a -> String -> IO a
requiredParseIO source p str =
  case parse p source str of
    Left err -> do
      hPutStrLn stderr $ "Parse error:\n" ++ errorBundlePretty err
      exitWith $ ExitFailure 2
    Right x -> pure x

parseGuard :: Bool -> Maybe String -> String -> Parser ()
parseGuard True _ _ = pure ()
parseGuard False unexpected expected =
  failure (fmap (Label . NonEmpty.fromList) unexpected) (Set.singleton (Label (NonEmpty.fromList expected)))

parseIdentifier :: Parser String
parseIdentifier = label "identifier" $ lexeme $ do
  ident <- liftA2 (:) letterChar (many identifierTailChar)

  parseGuard (ident `notElem` keywords) (Just ident) "identifier"

  pure ident
  where
    identifierTailChar :: Parser Char
    identifierTailChar = char '\'' <|> char '_' <|> alphaNumChar

keywords :: [String]
keywords = ["forall"]

parseRuleName :: Parser String
parseRuleName = label "rule name" $ lexeme $ between (symbol "{") (symbol "}") (some (anySingleBut '}'))

