--
-- | One-hole "evaluation contexts"
-- 
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}

module Egret.Rewrite.Context
  where

import           Data.Fix
import           Data.Void

import           Data.Bifunctor
import           Data.Functor.Product
import           Data.Functor.Compose
import           Data.Constraint

type family Sing :: k -> *

class SingI a where
  sing :: Sing a

data Nat = Z | S Nat
  deriving (Show)

data Fin (n :: Nat) where
  FinZ :: Fin Z
  FinS :: Fin n -> Fin (S n)

deriving instance Show (Fin n)

type instance Sing = Fin

instance SingI Z where
  sing = FinZ

instance SingI n => SingI (S n) where
  sing = FinS sing

instance SingI n :=> SingI (S n) where
  ins = Sub Dict

singStandard0 :: Fin n -> Dict (SingI n)
singStandard0 FinZ = Dict
singStandard0 (FinS x) =
  case singStandard0 x of
    Dict -> Dict

singStandard1 :: Fin (S n) -> Dict (SingI n)
singStandard1 (FinS x) =
  case singStandard0 x of
    Dict -> Dict

singStandard :: forall n. SingI (S n) :- SingI n
singStandard = Sub $
  case singStandard1 (sing @(S n)) of
    Dict -> Dict

type family Path n where
  Path Z     = ()
  Path (S n) = Either () (Path n)

pattern Here = ()

pattern L :: () -> Either () b
pattern L x = Left x

pattern R :: b -> Either () b
pattern R x = Right x

-- type family Prod n a where
--   Prod Z a = ()
--   Prod (S n) a = (a, Prod n a)

data Prod n a where
  ProdZ :: Prod Z a
  ProdS :: a -> Prod n a -> Prod (S n) a

data EditedProduct n a where
  EditedProduct :: Path n -> Prod n a -> EditedProduct n a

class Fill f g | f -> g where
  fill :: f a -> a -> g a

instance forall n. SingI n => Fill (EditedProduct n) (Prod (S n)) where
  fill (EditedProduct ix p) x =
    case sing @n of
      FinZ -> ProdS x p
      FinS (fin' :: Fin n') ->
        case ix of
          Left () -> ProdS x p
          Right ix' ->
            case p of
              ProdS y p' ->
                case singStandard @n' of
                  Sub Dict -> ProdS y $ fill (EditedProduct ix' p') x


-- class Diff f where
--   type Deriv f a = r | r -> f
--
--   diff :: a -> Deriv f a
--   fill :: Deriv f a -> a -> a

-- data EditPair f e
--   = EditR (Fix (f (EditPair f e))) e
--   | EditL e (Fix (f (EditPair f e)))
--
-- newtype JoinedProduct f a = JoinedProduct (Product f f a)
--
-- newtype JoinedFix (f :: (* -> * -> *) -> * -> *) =
--   JoinedFix (Fix (f (JoinedProduct (JoinedFix f))))
--
-- -- instance Bifunctor (EditPair e) where
-- --   bimap f _ (EditR x y) = EditR (f x) y
-- --   bimap _ g (EditL x y) = EditL x (g y)
--
-- -- editMap :: (e -> e') -> EditPair e a b -> EditPair e' a b
-- -- editMap f (EditR x y) = EditR x (f y)
-- -- editMap f (EditL x y) = EditL (f x) y
--
-- -- editAct :: (e -> r) -> (e -> r') -> EditPair e a b -> (r, r')
-- -- editAct = undefined
--
-- -- | A `Functor` with exactly one edit
-- data Edited (f :: (* -> * -> *) -> * -> *) e
--   = EditThere (f (JoinedFix f) (Edited f e))
--   | EditHere (f (EditPair f e) (JoinedFix f))
--
-- class MFunctor2 f where
--   hoist2 :: Bifunctor m => (forall a b. m a b -> n a b) -> f m r -> f n r
--
-- fill :: (MFunctor2 f, Functor (f (,))) => Edited f e -> e -> Fix (f (,))
-- fill (EditHere x) y =
--   let z = hoist2 undefined x
--   in
--   Fix $ undefined


-- -- | A Functor with a possible edits
-- data EditContext f
--   = InContext (f (EditContext f))
--   | Edit (Fix f) (Fix f)
--   | NoEdit (Fix f)
--
-- -- data Context f
-- --   = InContext (f (Context f))
-- --   | Hole (Fix f)
-- --
-- -- newtype ContextFix f = ContextFix (f (Context f))
-- --
-- -- fill :: Monad f => ContextFix f -> Fix f -> Fix f
-- -- fill (ContextFix c) x = Fix $ fmap (`fill` x) c
-- -- -- fill (Hole h) x = 
-- --
