{-# LANGUAGE DataKinds, GADTs, KindSignatures, TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Data.Fin (
  Finite (..)
) where

import Data.Nat
import Data.SNat (Natural)
import Data.Type.Equality ((:~:) (Refl))

import Prelude hiding (succ)

class Finite fin where
  zero :: fin (S n)
  succ :: fin n -> fin (S n)
  
  elimFin :: (forall m. p (S m))
    -> (forall m. n ~ S m => fin m -> p n) 
    -> fin n -> p n

  foldFin :: (forall m. p m -> p (S m))
          -> (forall m. p (S m))
          -> fin n -> p n
  foldFin f z = elimFin z (\n -> f (foldFin f z n))

  weaken :: fin n -> fin (S n)
  weaken = unSucc . foldFin succer (Succ zero)
    where
    succer :: Succ fin n -> Succ fin (S n)
    succer (Succ n) = Succ (succ n)

  weakenN :: forall n. forall k.  fin k -> fin (k + n)
  weakenN = unPlus . foldFin plusser (Plus zero)
    where
    plusser :: Plus fin n i -> Plus fin n (S i)
    plusser (Plus i) = Plus (succ i)

  plus :: fin (S m) -> fin (S n) -> fin (S (m + n))
  --times :: pnat (S m) -> pnat (S n) -> pnat (S (m * n))

  toIntegral :: forall i. forall n. Integral i => fin n -> i
  toIntegral = unConst . foldFin plus1 (Const 0)
    where
    plus1 :: Const i m -> Const i (S m)
    plus1 (Const x) = Const (x + 1)

newtype Const a (b :: PNat) = Const { unConst :: a }
newtype Succ fin n = Succ { unSucc :: fin (S n) }
newtype Plus fin n k = Plus { unPlus :: fin (k + n) }
