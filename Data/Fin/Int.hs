{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators #-}
{-# LANGUAGE RankNTypes #-}

module Data.Fin.Int where

import Data.Fin
import Data.Nat

import Data.Type.Equality ((:~:) (Refl))

import Unsafe.Coerce (unsafeCoerce)

data Fin :: PNat -> * where
  F :: { finToInt :: Int } -> Fin n

fz :: Fin (S n)
fz = F 0

fs :: Fin n -> Fin (S n)
fs (F n) = F (n + 1)

fin :: (forall m. p (S m))
    -> (forall m. n ~ S m => Fin m -> p n) 
    -> Fin n -> p n
fin z s (F n) = if n == 0
  then unsafeCoerce z
  else assumeNIsSuccF (unsafeCoerce Refl) s (F (n - 1))

assumeNIsSuccF :: n :~: S m -> (forall i. n ~ S i => Fin i -> p n)
  -> Fin m -> p n
assumeNIsSuccF Refl f x = f x

instance Finite Fin where
  zero = fz
  succ = fs

  elimFin = fin

  plus (F i) (F j) = unsafeCoerce (F (i + j))

  toIntegral = unConst . foldFin plus1 (Const 0)
    where
    plus1 :: Integral i => Const i m -> Const i (S m)
    plus1 (Const x) = Const (x + 1)

newtype Const a (b :: PNat) = Const { unConst :: a }

instance Show (Fin n) where
  show = show . finToInt
