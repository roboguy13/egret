module Egret.Parser.Type
  (parseType
  ,parseTypeSig
  )
  where

import           Egret.TypeChecker.Type

import           Egret.Parser.Utils

import           Text.Megaparsec

parseType :: Parser Type
parseType =
  try parseFnType <|> parseType'

parseType' :: Parser Type
parseType' = lexeme $
  try (symbol "(" *> parseType <* symbol ")")
    <|>
  parseBaseType

parseBaseType :: Parser Type
parseBaseType = label "base type" $ lexeme $ fmap BaseType parseIdentifier

parseFnType :: Parser Type
parseFnType = label "function type" $ lexeme $ do
  a <- parseType'
  symbol "->"
  FnType a <$> parseType

parseTypeSig :: Parser TypeSig
parseTypeSig = label "type signature" $ lexeme $ do
  ident <- parseIdentifier
  symbol "::"
  TypeSig ident <$> parseType

