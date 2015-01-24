{-# LANGUAGE TypeFamilies, TypeOperators, DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.PNat where

import qualified GHC.TypeLits as TL
import Data.Type.Equality ((:~:) (..), gcastWith)

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

data PNatS :: PNat -> * where
  SZ :: PNatS Z
  SS :: PNatS n -> PNatS (S n)

one :: PNatS One
one = SS SZ
two :: PNatS Two
two = SS one
three :: PNatS Three
three = SS two
four :: PNatS Four
four = SS three
five :: PNatS Five
five = SS four
six :: PNatS Six
six = SS five
seven :: PNatS Seven
seven = SS six
eight :: PNatS Eight
eight = SS seven
nine :: PNatS Nine
nine = SS eight
ten :: PNatS Ten
ten = SS nine

plus :: PNatS m -> PNatS n -> PNatS (m + n)
plus SZ n = n
plus (SS m) n = SS (plus m n)
