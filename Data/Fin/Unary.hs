{-# LANGUAGE DataKinds, GADTs, KindSignatures, TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Fin.Unary (
  Fin (..)
) where

import Data.Nat
import Data.Fin

data Fin :: PNat -> * where
  FZ :: Fin (S n)
  FS :: Fin n -> Fin (S n)

finToInteger :: Fin n -> Integer
finToInteger x = case x of
  FZ -> 1
  FS n -> let i = finToInteger n in i `seq` 1 + i

instance Show (Fin n) where
  show = show . finToInteger

instance Finite Fin where
  zero = FZ
  succ = FS

  elimFin z s n = case n of
    FZ -> z
    FS n' -> s n'

  --times :: pnat m -> pnat n -> pnat (m * n + m + n)
