{-# LANGUAGE TypeFamilies, TypeOperators, DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.SNat (
  Natural (..)
) where

import Data.Nat

import Data.Type.Equality (gcastWith, (:~:) (Refl))
import qualified GHC.TypeLits as TL
import Unsafe.Coerce (unsafeCoerce)

import Prelude hiding (succ)

class Natural pnat where
  zero :: pnat Z
  succ :: pnat n -> pnat (S n)
  elimNat :: forall p. forall n. (n ~ Z => p n)
          -> (forall m. n ~ S m => pnat m -> p n) 
          -> pnat n -> p n
  foldNat :: (forall m. p m -> p (S m) )
          -> p Z
          -> pnat n -> p n
  foldNat f z = elimNat z (\n -> f (foldNat f z n))

  plus :: pnat m -> pnat n -> pnat (m + n)
  plus m n = unOpResult $ 
    foldNat (OpResult . succ . unOpResult) (OpResult n) m

  times :: forall m. forall n. pnat m -> pnat n -> pnat (m * n)
  times m n = unOpResult2 $
    foldNat acc (OpResult2 zero) m where
    acc :: OpResult2 pnat n i -> OpResult2 pnat n (S i)
    acc (OpResult2 x) = OpResult2 (plus n x)

  pow :: forall m. forall n. pnat m -> pnat n -> pnat (m ^ n)
  pow m n = unPowResult $
    foldNat acc (PowResult one) n where
    acc :: PowResult pnat m i -> PowResult pnat m (S i)
    acc (PowResult x) = PowResult (times m x)

  equal :: forall m. forall n. pnat m -> pnat n -> Maybe (m :~: n)
  equal m n = unEqResult . unSwap $ elimNat zCase
    sCase
    m
    where
    zCase :: m ~ Z => Swap EqResult n m
    zCase = Swap (elimNat (EqResult (Just Refl)) 
                          (const $ EqResult Nothing) n)
    sCase :: m ~ S i => pnat i -> Swap EqResult n m
    sCase i = Swap (elimNat (EqResult Nothing) 
                   (\j -> EqResult (fmap succIt (equal i j))) n)
    succIt :: i :~: j -> S i :~: S j
    succIt Refl = Refl

  lte :: pnat m -> pnat n -> Maybe (LTE m n :~: True)
  lte m n = case lteHelper m n of
     LTEResult y -> y
    where
    lteHelper :: forall m. forall n. pnat m -> pnat n -> LTEResult m n
    lteHelper m n = case elimNat zCase sCase m of
      Swap y -> y
      where
      zCase :: m ~ Z => Swap LTEResult i m
      zCase = Swap (LTEResult (Just Refl))
      sCase :: pnat x -> Swap LTEResult n (S x)
      sCase i = Swap $ elimNat (LTEResult Nothing)
                 (\j -> succItt (lteHelper i j)) n
      succItt :: LTEResult i j -> LTEResult (S i) (S j)
      succItt (LTEResult (Just Refl)) = LTEResult (Just Refl)
      succItt (LTEResult Nothing) = LTEResult Nothing

  one :: pnat One
  one = succ zero

  two :: pnat Two
  two = plus one one

  three :: pnat Three
  three = plus two one

  four :: pnat Four
  four = times two two

  five :: pnat Five
  five = plus four one

  six :: pnat Six
  six = times three two

  seven :: pnat Seven
  seven = plus six one

  eight :: pnat Eight
  eight = times four two

  nine :: pnat Nine
  nine = times three three

  ten :: pnat Ten
  ten = times five two

  toIntegral :: forall i. forall n. Integral i => pnat n -> i
  toIntegral = unConst . foldNat plus1 (Const 0)
    where
    plus1 :: Const i m -> Const i (S m)
    plus1 (Const x) = Const (x + 1)

newtype EqResult (m :: PNat) (n :: PNat) = EqResult { unEqResult :: Maybe (m :~: n) }
newtype LTEResult (m :: PNat) (n :: PNat) = LTEResult { unLTEResult :: Maybe (LTE m n :~: True) }
newtype Swap f (a :: PNat) (b :: PNat) = Swap { unSwap :: f b a }

newtype Const a (b :: PNat) = Const { unConst :: a }

newtype OpResult pnat n m = OpResult { unOpResult :: pnat (m + n) }
newtype OpResult2 pnat n m = OpResult2 { unOpResult2 :: pnat (m * n) }
newtype PowResult pnat m n = PowResult { unPowResult :: pnat (m ^ n) }

newtype PSRS n m = PSRS { unPSRS :: S (m + n) :~: m + S n }

plusSuccRightSucc :: forall m n nat. Natural nat => nat m -> nat n
  -> S (m + n) :~: m + S n
plusSuccRightSucc m n = unPSRS (foldNat succer (PSRS Refl) m)
  where
  succer :: PSRS n i -> PSRS n (S i)
  succer (PSRS Refl) = PSRS Refl

newtype NPZN n = NPZN { unNPZN :: n :~: n + Z }

nPlusZIsN :: forall n nat. Natural nat => nat n -> n :~: n + Z
nPlusZIsN = unNPZN . foldNat succer (NPZN Refl)
  where
  succer :: NPZN i -> NPZN (S i)
  succer (NPZN Refl) = NPZN Refl

