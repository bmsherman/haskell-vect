{-# LANGUAGE TypeFamilies, TypeOperators, DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Data.SNat.Unary where

import Data.Nat
import Data.SNat

import Data.Type.Equality ((:~:) (Refl), gcastWith)

data SNat :: PNat -> * where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

instance Natural SNat where
  zero = SZ
  succ = SS
  elimNat z s n = case n of
    SZ -> z
    SS m -> s m

  plus SZ n = n
  plus (SS m) n = SS (plus m n)

  times SZ n = SZ
  times (SS m) n = plus n (times m n)

  toIntegral SZ = 0
  toIntegral (SS n) = 1 + toIntegral n
  {-# SPECIALIZE toIntegral :: SNat n -> Int #-}
  {-# SPECIALIZE toIntegral :: SNat n -> Integer #-}


minus :: LTE m n ~ True => SNat n -> SNat m -> SNat (n - m)
minus n SZ = n
minus (SS n) (SS m) = minus n m

foldSNatN :: (forall m. p m -> p (S m)) -> p Z -> SNat n -> p n
foldSNatN f z SZ = z
foldSNatN f z (SS n) = f (foldSNatN f z n)

