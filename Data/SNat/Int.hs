{-# LANGUAGE GADTs, KindSignatures, DataKinds, TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.SNat.Int where

import Data.Nat
import Data.SNat

import Data.Type.Equality ((:~:) (Refl), gcastWith)

import Unsafe.Coerce (unsafeCoerce)

newtype PNatS :: PNat -> * where
  N :: { toInt :: Int } -> PNatS n

pNatS :: forall p. forall n. (n ~ Z => p n) 
      -> (forall m. n ~ S m => PNatS m -> p n) 
      -> PNatS n -> p n
pNatS z s (N i) = if i == 0 
  then gcastWith (unsafeCoerce Refl :: n :~: Z) z
  else assumeNIsSucc (unsafeCoerce Refl) s (N (i - 1))

instance Natural PNatS where
  zero = N 0
  succ (N i) = N (i + 1)
  elimNat = pNatS

  plus (N i) (N j) = unsafeCoerce (N (i + j))
  times (N i) (N j) = unsafeCoerce (N (i * j))
  pow (N i) (N j) = unsafeCoerce (N (i ^ j))

  equal (N i) (N j) = if i == j
    then Just (unsafeCoerce Refl)
    else Nothing

  lte (N i) (N j) = if i <= j
    then Just (unsafeCoerce Refl)
    else Nothing

  one = N 1
  two = N 2
  three = N 3
  four = N 4
  five = N 5
  six = N 6
  seven = N 7
  eight = N 8
  nine = N 9
  ten = N 10

  toIntegral (N i) = fromIntegral i


assumeNIsSucc :: n :~: S m -> (forall i. n ~ S i => PNatS i -> p n) ->
  PNatS m -> p n
assumeNIsSucc Refl f x = f x

