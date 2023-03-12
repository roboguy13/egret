module Egret.Parser.RulesFile
  (RulesFile (..)
  ,parseRulesFile
  )
  where

import           Egret.TypeChecker.Type

import           Egret.Rewrite.Equation
import           Egret.Rewrite.Expr

import           Egret.Parser.Equation
import           Egret.Parser.Type

import           Egret.Parser.Utils

import           Control.Applicative

data RulesFile =
  RulesFile
    { _rulesFileSigs :: [TypeSig]
    , _rulesFileEqnDb :: EquationDB String
    }
  deriving (Show)

instance Semigroup RulesFile where
  RulesFile x1 y1 <> RulesFile x2 y2 = RulesFile (x1 <> x2) (y1 <> y2)

instance Monoid RulesFile where
  mempty = RulesFile mempty mempty

parseRulesFile :: Parser RulesFile
parseRulesFile = do
  optional sc
  mconcat <$> some (parseTypeSig' <|> parseEquationDef')

parseTypeSig' :: Parser RulesFile
parseTypeSig' = lexeme $ do
  typeSig <- parseTypeSig
  pure $ RulesFile [typeSig] []

parseEquationDef' :: Parser RulesFile
parseEquationDef' = lexeme $ do
  eqnDef <- parseEquationDef
  pure $ RulesFile [] [eqnDef]

