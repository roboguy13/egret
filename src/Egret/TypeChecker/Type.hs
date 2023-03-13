-- | NOTE: This module strategically avoids exporting certain
-- definitions to ensure certain invariants always hold

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}

module Egret.TypeChecker.Type
  (Type (..)
  ,Typed (..)
  ,Name

  ,TypeSig (..)
  ,TypedExpr'
  ,TypedExpr

  ,pattern TypedApp
  ,pattern TypedV

  ,TypeEnv'
  ,TypeEnv

  ,withTypeSigs

  ,extendTypeEnv

  ,TypedScopedExpr
  ,fromTypedScope

  ,getType
  ,unTyped

  ,exprHoles

  ,typeInferScoped
  ,typeCheckScoped
  ,typeInfer
  ,typeCheck

  ,BoundSubst
  ,emptyBoundSubst
  ,mkBoundSubst
  ,applyBoundSubst
  ,BoundSubstResult (..)
  ,boundSubstLookup
  )
  where

import           Egret.Ppr

import           Egret.Rewrite.Expr
import           Egret.Rewrite.Rewrite

import           Control.Monad.Reader

import           Control.Comonad.Store

import           Control.Lens.Plated

import           Control.Applicative
import           Data.Data

import           Control.Lens.Internal.Context

import           Data.Coerce

import           Bound
import           Bound.Scope

import Debug.Trace

data Type
  = BaseType String
  | FnType Type Type
  deriving (Show, Eq)

instance Ppr Type where
  pprDoc (BaseType str) = text str
  pprDoc (FnType a b) = sep [pprDoc a, text "->", pprDoc b]

data Typed a = Typed Type a
  deriving (Show, Functor)

unTyped :: Typed a -> a
unTyped (Typed _ a) = a

type Name = Typed String

-- | Don't display the type part of a 'Typed'
instance Ppr a => Ppr (Typed a) where
  pprDoc (Typed _ x) = pprDoc x

data TypeSig = TypeSig String Type
  deriving (Show)

withTypeSigs :: [TypeSig] -> (forall tyenv. TypeEnv tyenv -> r) -> r
withTypeSigs sigs k = k $ TypeEnv $ map go sigs
  where
    go (TypeSig x y) = (x, y)

withTypeds :: [Typed String] -> (forall tyenv. TypeEnv tyenv -> r) -> r
withTypeds bnds k = k $ foldr (flip tcExtend . (:[])) (TypeEnv []) bnds

-- -- | Don't export value constructor
-- data a :< b = TypeEnvContains

data a :> b

extendTypeEnv :: [Typed String] -> TypeEnv tyenv -> (forall tyenv2. TypeEnv tyenv2 -> r) -> r
extendTypeEnv bnds env k = k (tcExtend env bnds)

-- disjointTypeEnvExtend :: TypeEnv tyenv1 -> TypeEnv tyenv2 -> Maybe (TypeEnv tyenv2, tyenv :< tyenv2)
-- disjointTypeEnvExtend = undefined

newtype TypeEnv' tyenv a = TypeEnv [(a, Type)]

type TypeEnv tyenv = TypeEnv' tyenv String

tcLookup :: Eq a => a -> TypeEnv' tyenv a -> Maybe Type
tcLookup v (TypeEnv env) = lookup v env

tcExtend :: TypeEnv' tyenv a -> [Typed a] -> TypeEnv' tyenv2 a
tcExtend (TypeEnv env) = TypeEnv . go
  where
    go [] = env
    go (Typed ty x : rest) = (x, ty) : go rest

-- disjointTcExtend :: TypeEnv tyenv -> [Typed String] -> Maybe (TypeEnv tyenv2, tyenv :< tyenv2)
-- disjointTcExtend env = undefined


type TypeCheck tyenv b = ReaderT (TypeEnv' tyenv b) (Either String)

errorExpected :: String -> String -> Either String a
errorExpected expected found =
  Left $ "Expected " ++ expected ++ ", found " ++ found

-- | By strategic exporting, we ensure that this will never fail
getType :: TypeEnv tyenv -> TypedExpr tyenv -> Type
getType env (TypedExpr e) =
  let Right (ty, _) = typeInfer env e
  in
  ty

typedExpr :: TypeEnv tyenv -> Expr String -> Either String (TypedExpr tyenv)
typedExpr env = fmap snd . typeInfer env

exprHoles :: forall tyenv.
  TypedExpr tyenv -> [Pretext (->) (TypedExpr tyenv) (TypedExpr tyenv) (TypedExpr tyenv)]
exprHoles = map coerce' . holes . coerce
  where
    coerce' :: Pretext (->) (Expr String) (Expr String) (Expr String) -> Pretext (->) (TypedExpr tyenv) (TypedExpr tyenv) (TypedExpr tyenv)
    coerce' p = Pretext $ coerce'' $ runPretext p

    coerce'' :: (forall f. Functor f => (->) (Expr String) (f (Expr String)) -> f (Expr String)) -> (forall f. Functor f => (->) (TypedExpr tyenv) (f (TypedExpr tyenv)) -> f (TypedExpr tyenv))
    coerce'' f g = TypedExpr <$> f (fmap getTypedExpr . g . TypedExpr)

-- | Do not export the value constructor
newtype TypedExpr' tyenv a = TypedExpr { getTypedExpr :: Expr a }
  deriving (Show, Eq)
type TypedExpr tyenv = TypedExpr' tyenv String


-- | We can pattern match on an well-typed 'App' to
-- get two well-typed 'App's (all under the same typing environment).
pattern TypedApp :: TypedExpr' tyenv a -> TypedExpr' tyenv a -> TypedExpr' tyenv a
pattern TypedApp x y <- TypedExpr (App (TypedExpr -> x) (TypedExpr -> y))

-- | Unidirectional for safety
pattern TypedV :: a -> TypedExpr' tyenv a
pattern TypedV x <- TypedExpr (V x)

type TypedScopedExpr tyenv = Scope Int (TypedExpr' tyenv)

fromTypedScope :: forall tyenv a. TypedScopedExpr tyenv a -> TypedExpr' tyenv (Var Int a)
fromTypedScope = TypedExpr . fromScope . coerce


newtype BoundSubst tyenv b a = BoundSubst [(b, TypedExpr' tyenv a)]
  deriving (Show)

emptyBoundSubst :: BoundSubst tyenv b a
emptyBoundSubst = BoundSubst []

applyBoundSubst :: Show a => BoundSubst tyenv Int a -> TypedScopedExpr tyenv a -> TypedExpr' tyenv a
applyBoundSubst env = TypedExpr . instantiate go . coerce
  where
    go i =
      case boundSubstLookup i env of
        BoundSubstFound x -> getTypedExpr x
        BoundSubstNotFound {} -> error $ "applyBoundSubst: Cannot find " ++ show i ++ " in " ++ show env

-- | Either we find it or we can safely insert it
data BoundSubstResult tyenv b a
  = BoundSubstFound (TypedExpr' tyenv a)
  | BoundSubstNotFound (TypedExpr' tyenv a -> BoundSubst tyenv b a)

boundSubstLookup :: Eq b => b -> BoundSubst tyenv b a -> BoundSubstResult tyenv b a
boundSubstLookup x (BoundSubst subst) =
  case lookup x subst of
    Nothing -> BoundSubstNotFound $ \e -> BoundSubst ((x, e) : subst)
    Just r -> BoundSubstFound r

mkBoundSubst :: (Eq a, Show a, Eq b, Show b) => TypeEnv' tyenv (Var b a) -> [(b, Expr a)] -> Maybe (BoundSubst tyenv b a)
mkBoundSubst tcEnv bnds =
        -- We temporarily wrap each variables in an 'F'...
    case traverse (go . fmap (fmap F)) bnds of
      Left {} -> Nothing
      Right bnds' -> Just $ BoundSubst bnds'
  where
    go (v, e) = do
      (ty, _) <- typeInfer tcEnv (V (B v))
      (_, TypedExpr e') <- typeCheck tcEnv e ty
        -- ... then remove the 'F's. This is safe since we put them
        -- everywhere to start with
      pure (v, TypedExpr (fmap unF e'))

    unF (F x) = x

typeInferScoped :: forall tyenv a b. (Eq a, Show a, Eq b, Show b) => TypeEnv' tyenv (Var b a) -> Scope b Expr a -> Either String (Type, Scope b (TypedExpr' tyenv) a)
typeInferScoped tcEnv sc =
    fmap (coerce' . toScope . getTypedExpr) <$> typeInfer tcEnv (fromScope sc)
  where
    coerce' :: Scope b Expr a -> Scope b (TypedExpr' tyenv) a
    coerce' = coerce

typeCheckScoped :: (Eq a, Eq b) => TypeEnv' tyenv (Var b a) -> Scope b Expr a -> Type -> Either String (Type, Scope b (TypedExpr' tyenv) a)
typeCheckScoped tcEnv sc ty =
    fmap (coerce' . toScope . getTypedExpr) <$> typeCheck tcEnv (fromScope sc) ty
  where
    coerce' :: Scope b Expr a -> Scope b (TypedExpr' tyenv) a
    coerce' = coerce

typeInfer :: (Eq a, Show a) => TypeEnv' tyenv a -> Expr a -> Either String (Type, TypedExpr' tyenv a)
typeInfer env e = (,TypedExpr e) <$> runReaderT (typeInfer' e) env

typeCheck :: (Eq a) => TypeEnv' tyenv a -> Expr a -> Type -> Either String (Type, TypedExpr' tyenv a)
typeCheck env e ty = (,TypedExpr e) <$> runReaderT (typeCheck' e ty) env

typeInfer' :: (Show a, Eq a) => Expr a -> TypeCheck tyenv a Type
typeInfer' (V a) =
  asks (tcLookup a) >>= \case
    Nothing -> lift $ Left $ "typeInfer': Cannot find variable " ++ show a
    Just ty -> pure ty
typeInfer' (App f x) = do
  typeInfer' f >>= \case
    FnType a b -> do
      typeCheck' x a
      pure b
    fTy -> lift $ errorExpected "function type" (ppr fTy)

typeCheck' :: Eq a => Expr a -> Type -> TypeCheck tyenv a Type
typeCheck' (V a) ty =
  asks (tcLookup a) >>= \case
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

