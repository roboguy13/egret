module Egret.Solver.Solver where

import           Egret.Solver.TreeSearch
import           Egret.Proof.Trace
import           Egret.TypeChecker.Expr
import           Egret.TypeChecker.Type
import           Egret.Rewrite.WellTyped
import           Egret.Tactic.Tactic

import           Egret.Rewrite.Equation

import           Egret.Solver.Backtrack

import           Control.Monad.Writer

data Rewritten tyenv =
  Rewritten
    (TypedExpr tyenv) -- | Old expression
    String -- | Rewrite name
    Direction
    Int -- | Where was it rewritten?
    (TypedExpr tyenv) -- | New expression

type SolverTreeSearch tyenv = TreeSearch (TraceSteps tyenv String) (TypedExpr tyenv) (Rewritten tyenv)

rewrittenResult :: Rewritten tyenv -> TypedExpr tyenv
rewrittenResult (Rewritten _ _ _ _ e') = e'

rewrittenOriginal :: Rewritten tyenv -> TypedExpr tyenv
rewrittenOriginal (Rewritten e _ _ _ _) = e

rewrittenToStep :: Rewritten tyenv -> ProofTraceStep tyenv String
rewrittenToStep (Rewritten e name dir ix _)
  | ix == 0 = ProofTraceStep e (RewriteTactic dir name)
  | otherwise = ProofTraceStep e (RewriteAtTactic ix dir name)

