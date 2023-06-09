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

import           Egret.TypeChecker.Type

import           Egret.Repl.Command

import           Egret.Solver.BruteForce

import           Egret.Ppr

import           System.IO
import           System.Exit

import           System.Console.Haskeline

import           Data.Maybe

repl :: ProofM tyenv String (InputT IO) ()
repl = forever $ do
  goal <- gets _currentGoal
  liftIO $ putStrLn $ "Current expression: " <> ppr goal

  lift (getInputLine "> ") >>= \case
    Nothing -> liftIO exitSuccess
    Just input -> do
      typeEnv <- asks _proofEnvTypeEnv

      case parse' parseCommand input of
        Left err ->
          liftIO $ putStrLn $ "Cannot parse command:\n" ++ err

        Right (RunTactic tactic) -> do
          applyTacticM tactic >>= \case
            Nothing ->
              liftIO $ putStrLn "Tactic failed"

            Just () -> pure ()

        Right (RunBruteForce fuelMaybe targetExpr) -> do
          eqnDb <- asks _proofEnvEqnDb

          let bruteForceConfig =
                case fuelMaybe of
                  Nothing -> defaultBruteForce
                  Just fuel -> defaultBruteForce { _bruteForceStartFuel = fuel }

          let go = do
                    (_, _, targetExpr') <- typeInfer typeEnv targetExpr
                    bruteForce typeEnv bruteForceConfig eqnDb (goal :=: targetExpr')

          case go of
            Left err -> liftIO $ putStrLn err
            Right tr -> do
              modify (<> tr)

        Right Undo -> do
          tr <- get
          case traceUndo tr of
            Left err -> liftIO $ putStrLn err
            Right newTr -> put newTr

        Right Log -> do
          tr <- get
          liftIO $ putStrLn $ ppr tr
          liftIO $ putStrLn ""

        Right Quit -> liftIO exitSuccess

