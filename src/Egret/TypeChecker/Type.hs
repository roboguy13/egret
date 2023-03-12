{-# LANGUAGE LambdaCase #-}

module Egret.TypeChecker.Type
  (Type (..)
  ,TypeEnv
  ,TypeSig (..)
  ,toTypeEnv
  ,mkAtRewrite
  ,rewriteAt
  ,allWellTypedRewrites
  ,ensureWellTypedRewrite
  ,typeInferEquation
  ,typeInfer
  ,typeCheck
  ,isWellTyped
  )
  where

import           Egret.Ppr

import           Egret.Rewrite.Expr
import           Egret.Rewrite.Rewrite
import           Egret.Rewrite.Equation

import           Control.Monad.Reader

import           Control.Comonad.Store

import           Control.Lens.Plated

import           Control.Applicative

import Debug.Trace

data Type
  = BaseType String
  | FnType Type Type
  deriving (Show, Eq)

instance Ppr Type where
  pprDoc (BaseType str) = text str
  pprDoc (FnType a b) = sep [pprDoc a, text "->", pprDoc b]

data TypeSig = TypeSig String Type
  deriving (Show)

toTypeEnv :: [TypeSig] -> TypeEnv
toTypeEnv = map go
  where
    go (TypeSig x y) = (x, y)

-- | Well-typed input ==> well-typed output
ensureWellTypedRewrite :: TypeEnv -> Rewrite Expr String -> Rewrite Expr String
ensureWellTypedRewrite env re = Rewrite $ \x ->
  let r = runRewrite re x
      b1 = not (isWellTyped env x)
      b2 = or (fmap (isWellTyped env) r)
  in
  if b1 || b2
    -- then trace ("well-typed implication: " ++ show (x, r)) r
    then r
    else trace ("not well-typed, " ++ show (b1,b2) ++ ": " ++ show (ppr x, fmap ppr r)) Nothing

allWellTypedRewrites :: TypeEnv -> Rewrite Expr String -> Expr String -> [Expr String]
allWellTypedRewrites typeEnv re fa = 
  maybeCons (rewriteHere (ensureWellTypedRewrite typeEnv re) fa)
    $ concatMap (experiment (allWellTypedRewrites typeEnv re)) (holes fa)

mkAtRewrite :: TypeEnv -> At (Rewrite Expr String) -> Rewrite Expr String
mkAtRewrite env = Rewrite . rewriteAt env

rewriteAt :: TypeEnv -> At (Rewrite Expr String) -> Expr String -> Maybe (Expr String)
rewriteAt env (At ix0 re) x =
    let res = allWellTypedRewrites env re x
    in
    traceShow (take 30 res) $ go ix0 res
  where
    go _ [] = Nothing
    go 0 (x:_) = Just x
    go ix (_:xs) = go (ix-1) xs


-- allRewrites :: Plated (f a) => Rewrite f a -> f a -> [f a]
-- allRewrites re fa =
--   maybeCons (rewriteHere re fa)
--     $ concatMap (experiment (allRewrites re)) (holes fa)

maybeCons :: Maybe a -> [a] -> [a]
maybeCons Nothing xs = xs
maybeCons (Just x) xs = x : xs

type TypeEnv = [(String, Type)]

type TypeCheck = ReaderT TypeEnv (Either String)

typeInferEquation :: TypeEnv -> Equation Expr String -> Either String Type
typeInferEquation env (lhs0 :=: rhs0) =
  go (lhs0 :=: rhs0) <|> go (rhs0 :=: lhs0)
  where
    go (lhs :=: rhs) =
      typeCheck env rhs =<< typeInfer env lhs

errorExpected :: String -> String -> Either String a
errorExpected expected found =
  Left $ "Expected " ++ expected ++ ", found " ++ found

isWellTyped :: TypeEnv -> Expr String -> Bool
isWellTyped env (V a) = True
isWellTyped env e =
  case typeInfer env e of
    Left {} -> False
    Right {} -> True

typeInfer :: TypeEnv -> Expr String -> Either String Type
typeInfer env e = runReaderT (typeInfer' e) env

typeCheck :: TypeEnv -> Expr String -> Type -> Either String Type
typeCheck env e ty = runReaderT (typeCheck' e ty) env

typeInfer' :: Expr String -> TypeCheck Type
typeInfer' (V a) =
  asks (lookup a) >>= \case
    Nothing -> lift $ Left $ "typeInfer': Cannot find variable " ++ a
    Just ty -> pure ty
typeInfer' (App f x) = do
  typeInfer' f >>= \case
    FnType a b -> do
      typeCheck' x a
      pure b
    fTy -> lift $ errorExpected "function type" (ppr fTy)

typeCheck' :: Expr String -> Type -> TypeCheck Type
typeCheck' (V a) ty =
  asks (lookup a) >>= \case
    Nothing -> pure ty
    Just ty'
      | ty' == ty -> pure ty
      | otherwise -> lift $ errorExpected (ppr ty) (ppr ty')

typeCheck' (App f x) ty =
  case ty of
    FnType a b -> do
      typeCheck' f a
      typeCheck' x b
      pure ty
    _ -> lift $ errorExpected "function type" (ppr ty)

