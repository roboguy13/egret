{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Egret.Ppr
  (Ppr (..)
  ,ppr
  ,module Text.PrettyPrint.HughesPJ
  )
  where

import           Text.PrettyPrint.HughesPJ hiding ((<>))

class Ppr a where
  pprDoc :: a -> Doc

ppr :: Ppr a => a -> String
ppr = show . pprDoc

instance Ppr String where pprDoc = text

