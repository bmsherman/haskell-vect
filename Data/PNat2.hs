{-# LANGUAGE TypeFamilies, TypeOperators, DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.PNat2 (
  Natural (..), PNat (..), type (+), type (*), type (^)
  , Fact (..)
  , LTE (..)
  , PNatS
  , One, Two, Three, Four, Five, Six, Seven, Eight, Nine, Ten
  , myInt
) where

import Data.Type.Equality (gcastWith, (:~:) (Refl))
import qualified GHC.TypeLits as TL
import Unsafe.Coerce (unsafeCoerce)

import Prelude hiding (succ)

data PNat = Z | S PNat deriving (Eq, Show, Ord)

type family One :: PNat where One = S Z
type family Two :: PNat where Two = S One
type family Three :: PNat where Three = S Two
type family Four :: PNat where Four = S Three
type family Five :: PNat where Five = S Four
type family Six :: PNat where Six = S Five
type family Seven :: PNat where Seven = S Six
type family Eight :: PNat where Eight = S Seven
type family Nine :: PNat where Nine = S Eight
type family Ten :: PNat where Ten = S Nine


infixl 6 +
type family (+) (m :: PNat) (n :: PNat) :: PNat where
  Z + n = n
  S m + n = S (m + n)

infixl 6 -
type family (-) (m :: PNat) (n :: PNat) :: PNat where
  m - Z = m
  S m - S n = m - n

infixl 7 *
type family (*) (m :: PNat) (n :: PNat) :: PNat where
  Z * n = Z
  S m * n = n + m * n

infixr 8 ^
type family (^) (m :: PNat) (n :: PNat) :: PNat where
  m ^ Z = S Z
  m ^ S n = m * (m ^ n)

type family Fact (n :: PNat) :: PNat where
  Fact Z = S Z
  Fact (S n) = Fact n * S n

type family Lit (n :: TL.Nat) :: PNat where
  Lit 0 = Z
  Lit n = S (Lit (n TL.- 1))

type family Cmp (m :: PNat) (n :: PNat) :: Ordering where
  Cmp Z Z = EQ
  Cmp m Z = GT
  Cmp Z n = LT
  Cmp (S m) (S n) = Cmp m n

type family LTE (m :: PNat) (n :: PNat) :: Bool where
  LTE Z n = True
  LTE (S m) Z = False
  LTE (S m) (S n) = LTE m n

newtype PNatS :: PNat -> * where
  N :: { toInt :: Int } -> PNatS n

pNatS :: forall p. forall n. (n ~ Z => p n) 
      -> (forall m. n ~ S m => PNatS m -> p n) 
      -> PNatS n -> p n
pNatS z s (N i) = if i == 0 
  then gcastWith (unsafeCoerce Refl :: n :~: Z) z
  else assumeNIsSucc (unsafeCoerce Refl) s (N (i - 1))

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

data EqResult (m :: PNat) (n :: PNat) = EqResult { unEqResult :: Maybe (m :~: n) }
data LTEResult (m :: PNat) (n :: PNat) = LTEResult { unLTEResult :: Maybe (LTE m n :~: True) }
data Swap f (a :: PNat) (b :: PNat) = Swap { unSwap :: f b a }

data Const a (b :: PNat) = Const { unConst :: a }

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


newtype OpResult pnat n m = OpResult { unOpResult :: pnat (m + n) }
newtype OpResult2 pnat n m = OpResult2 { unOpResult2 :: pnat (m * n) }
newtype PowResult pnat m n = PowResult { unPowResult :: pnat (m ^ n) }

assumeNIsSucc :: n :~: S m -> (forall i. n ~ S i => PNatS i -> p n) ->
  PNatS m -> p n
assumeNIsSucc Refl f x = f x

