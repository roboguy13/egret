{-# LANGUAGE LambdaCase #-}

module Main
  (main
  )
  where

import           Egret.Repl.Repl

import           Egret.Proof.State

import           Egret.Parser.Equation
import           Egret.Parser.Expr
import           Egret.Parser.RulesFile
import           Egret.Parser.Utils

import           Egret.TypeChecker.Type

import           Egret.Rewrite.Equation

import           System.IO
import           System.Environment
import           System.Exit

main :: IO ()
main = do
  ruleFileName <- getRuleFileName
  (typeEnv, ruleDb) <- parseRules ruleFileName

  -- print typeEnv
  putStr "Enter initial expression: "
  hFlush stdout
  initialGoal <- requiredParseIO "<stdin>" parseExpr =<< getLine
  runProofM typeEnv ruleDb initialGoal repl

getRuleFileName :: IO String
getRuleFileName =
  getArgs >>= \case
    [x] -> pure x
    xs -> do
      hPutStrLn stderr $ "Expected exactly one argument (the rule file name). Got " ++ show (length xs)
      exitWith $ ExitFailure 1

parseRules :: String -> IO (TypeEnv, EquationDB String)
parseRules fileName = do
  rulesFile <- requiredParseIO fileName parseRulesFile =<< readFile fileName
  pure (toTypeEnv (_rulesFileSigs rulesFile), _rulesFileEqnDb rulesFile)

-- parseRuleDb :: String -> IO (EquationDB String)
-- parseRuleDb fileName =
--   requiredParseIO fileName parseEquationDefs =<< readFile fileName

