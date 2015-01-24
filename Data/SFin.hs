{-# LANGUAGE DataKinds, GADTs, KindSignatures, TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Data.SFin (
  Fin, finToInt, fzero, fsucc
) where

import Data.SNat
import GHC.TypeLits

data Fin :: Nat -> * where
  MkFin :: Int -> Fin n

fzero :: Fin n
fzero = MkFin 0

fsucc :: Fin n -> Fin (1 + n)
fsucc (MkFin n) = MkFin (1 + n)

finToInt :: Fin n -> Int
finToInt (MkFin x) = x

instance Show (Fin n) where
  show = show . finToInt
