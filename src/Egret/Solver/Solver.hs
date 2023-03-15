module Egret.Solver.Solver where

import           Egret.Solver.TreeSearch
import           Egret.Proof.Trace
import           Egret.TypeChecker.Expr
import           Egret.TypeChecker.Type
import           Egret.Rewrite.WellTyped

import           Control.Monad.Writer

type SolverTreeSearch tyenv = TreeSearch (TraceWriter tyenv String) (TypedExpr tyenv) (WellTypedRewrite tyenv)
type SolverResult tyenv = Result (TraceWriter tyenv String) (TypedExpr tyenv)

