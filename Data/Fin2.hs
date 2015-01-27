{-# LANGUAGE DataKinds, GADTs, KindSignatures, TypeOperators #-}
{-# LANGUAGE RankNTypes #-}

module Data.Fin2 (
  Fin, fz, fs, fin, foldFin
) where

import Data.PNat2
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

foldFin :: (forall m. p m -> p (S m))
        -> (forall m. p (S m))
        -> Fin n -> p n
foldFin f z = fin z (\n -> f (foldFin f z n))

assumeNIsSuccF :: n :~: S m -> (forall i. n ~ S i => Fin i -> p n)
  -> Fin m -> p n
assumeNIsSuccF Refl f x = f x

instance Show (Fin n) where
  show = show . finToInt
