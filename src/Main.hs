{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

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
import           Egret.TypeChecker.Equation

import           Egret.Rewrite.Equation

import           System.IO
import           System.Environment
import           System.Exit

import           System.Console.Haskeline

main :: IO ()
main = do
  ruleFileName <- getRuleFileName

  withParsedRules ruleFileName $ \(tcEnv, ruleDb) -> do
    print tcEnv

    ruleDb' <- runChecked $ checkEquationDb tcEnv ruleDb

    putStr "Enter initial expression: "
    hFlush stdout
    initialGoal <- requiredParseIO "<stdin>" parseExpr =<< getLine

    (_, extendedTcEnv, initialGoal') <- runChecked $ typeInfer tcEnv initialGoal

    runTypeEnvExtended extendedTcEnv $ \tcEnvIncl tcEnv' -> do

        -- TODO: Use the TyEnv inclusion so that we don't need to type
        -- check again
      ruleDb'' <- runChecked $ checkEquationDb tcEnv' ruleDb
      (_, _, initialGoal'') <- runChecked $ typeInfer tcEnv' initialGoal

      runInputT defaultSettings $ runProofM tcEnv' ruleDb'' initialGoal'' repl

getRuleFileName :: IO String
getRuleFileName =
  getArgs >>= \case
    [x] -> pure x
    xs -> do
      hPutStrLn stderr $ "Expected exactly one argument (the rule file name). Got " ++ show (length xs)
      exitWith $ ExitFailure 1

withParsedRules :: String -> (forall tyenv. (TypeEnv tyenv, EquationDB String) -> IO r) -> IO r
withParsedRules fileName k = do
  rulesFile <- requiredParseIO fileName parseRulesFile =<< readFile fileName

  withTypeSigs (_rulesFileSigs rulesFile) $ \tcEnv ->
    k (tcEnv, _rulesFileEqnDb rulesFile)

checkEquationDb :: TypeEnv tyenv -> EquationDB String -> Either String (TypedEquationDB tyenv)
checkEquationDb tcEnv = mapM go
  where
    go (name, eq) =
      let tcEnv' = localTypeEnv tcEnv $ forallQuantifiedVarsDeBruijn eq
      in
        fmap (name,) (toTypedQEquation tcEnv' eq)

runChecked :: Either String a -> IO a
runChecked (Left err) = putStrLn err *> exitWith (ExitFailure 3)
runChecked (Right x) = pure x

