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

import           Egret.Ppr

import           System.IO

repl :: ProofM String IO ()
repl = forever $ do
  goal <- gets _currentGoal
  liftIO $ putStrLn $ ppr goal

  liftIO $ putStr "> "
  liftIO $ hFlush stdout

  input <- liftIO getLine

  case parse' parseTactic input of
    Left err ->
      liftIO $ putStrLn $ "Cannot parse tactic:\n" ++ err

    Right tactic -> do
      applyTacticM tactic >>= \case
        Nothing ->
          liftIO $ putStrLn "Tactic failed"

        Just () -> repl

