{-# LANGUAGE LambdaCase #-}

module Egret.Repl.Repl
  (repl
  )
  where

import           Egret.Proof.State
import           Egret.Rewrite.Equation

import           Text.Megaparsec

import           Egret.Parser.Utils
import           Egret.Parser.Tactic

import           Egret.Repl.Command

import           Egret.Solver.BruteForce

import           Egret.Ppr

import           System.IO

repl :: ProofM String IO ()
repl = forever $ do
  goal <- gets _currentGoal
  liftIO $ putStrLn $ ppr goal

  liftIO $ putStr "> "
  liftIO $ hFlush stdout

  input <- liftIO getLine

  case parse' parseCommand input of
    Left err ->
      liftIO $ putStrLn $ "Cannot parse tactic:\n" ++ err

    Right (RunTactic tactic) -> do
      applyTacticM tactic >>= \case
        Nothing ->
          liftIO $ putStrLn "Tactic failed"

        Just () -> repl

    Right (RunBruteForce fuelMaybe targetExpr) -> do
      eqnDb <- ask
      case bruteForce defaultBruteForce eqnDb (goal :=: targetExpr) of
        Left err -> liftIO $ putStrLn err
        Right tr -> do
          modify (<> tr)
          repl

