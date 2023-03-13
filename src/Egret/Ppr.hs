{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Egret.Ppr
  (Ppr (..)
  ,ppr
  ,module Text.PrettyPrint.HughesPJ
  )
  where

import           Text.PrettyPrint.HughesPJ hiding ((<>))

import           Bound

class Ppr a where
  pprDoc :: a -> Doc

ppr :: Ppr a => a -> String
ppr = show . pprDoc

instance Ppr String where pprDoc = text
instance Ppr Int where pprDoc = text . show
instance (Ppr a, Ppr b) => Ppr (Var b a) where
  pprDoc (F x) = pprDoc x
  pprDoc (B y) = text "#" <> pprDoc y

