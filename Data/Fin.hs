{-# LANGUAGE DataKinds, GADTs, KindSignatures, TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Data.Fin (
  Fin (..)
) where

import Data.PNat
import Data.SNat hiding (lit)

data Fin :: PNat -> * where
  FZ :: Fin n
  FS :: Fin n -> Fin (S n)

finToInteger :: Fin n -> Integer
finToInteger x = case x of
  FZ -> 1
  FS n -> let i = finToInteger n in i `seq` 1 + i

instance Show (Fin n) where
  show = show . finToInteger
