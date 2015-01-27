{-# LANGUAGE DataKinds, KindSignatures, GADTs, TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Vect2 where

import Data.Fin as F
import Data.Nat
import Data.SNat as N

import Data.Proxy (Proxy (..))
import Data.Type.Equality ((:~:) (Refl), gcastWith)
import Prelude (Show (show), (.), Bool (..), undefined, Maybe (..), ($)
       , Functor (fmap), Eq (..), Ord (..), Ordering (..), Num (..)
       , (&&), (||), max, min, const)

infixr 5 :.
data Vect :: PNat -> * -> * where
  Nil  :: Vect Z a
  (:.) :: a -> Vect n a -> Vect (S n) a

instance Show a => Show (Vect n a) where
  show = show . toList

instance Functor (Vect n) where
  fmap = map

instance Eq a => Eq (Vect n a) where
  Nil == Nil = True
  x :. xs == y :. ys = x == y && xs == ys

instance Ord a => Ord (Vect n a) where
  compare Nil Nil = EQ
  compare (x :. xs) (y :. ys) = case compare x y of
    LT -> LT
    EQ -> compare xs ys
    GT -> GT

toList :: Vect n a -> [a]
toList Nil = []
toList (x :. xs) = x : toList xs

(++) :: Vect m a -> Vect n a -> Vect (m + n) a
Nil ++ ys = ys
(x :. xs) ++ ys = x :. (xs ++ ys)

head :: Vect (S n) a -> a
head (x :. xs) = x

last :: Vect (S n) a -> a
last (x :. ys) = case ys of
  Nil    -> x
  _ :. _ -> last ys

tail :: Vect (S n) a -> Vect n a
tail (x :. xs) = xs

init :: Vect (S n) a -> Vect n a
init (x :. ys) = init' x ys
  where
  init' :: a -> Vect n a -> Vect n a
  init' _ Nil = Nil
  init' y (z :. zs) = y :. init' z zs

null :: Vect n a -> Bool
null Nil = True
null (_ :. _) = False

length :: Natural pnat => Vect n a -> pnat n
length Nil = N.zero
length (_ :. xs) = N.succ (length xs)

map :: (a -> b) -> Vect n a -> Vect n b
map f Nil = Nil
map f (x :. xs) = f x :. map f xs

nPlusZIsN :: Vect n a -> Vect n a :~: Vect (n + Z) a
nPlusZIsN Nil = Refl
nPlusZIsN (x :. xs) = gcastWith (nPlusZIsN xs) Refl

plusSuccRightSucc :: Vect n a -> Vect m a
  -> Vect (S (n + m)) a :~: Vect (n + S m) a
plusSuccRightSucc Nil ys = Refl
plusSuccRightSucc (x :. xs) ys = gcastWith (plusSuccRightSucc xs ys) Refl

reverse :: Vect n a -> Vect n a
reverse zs = gcastWith (nPlusZIsN zs) (go Nil zs) where
  go :: Vect m xs -> Vect n xs -> Vect (n + m) xs
  go acc Nil = acc
  go acc (x :. xs) = gcastWith (plusSuccRightSucc xs acc) (go (x :. acc) xs)

type family Interspersed (n :: PNat) :: PNat where
  Interspersed Z = Z
  Interspersed (S Z) = S Z
  Interspersed (S n) = S (S (Interspersed n))

intersperse :: a -> Vect n a -> Vect (Interspersed n) a
intersperse x Nil = Nil
intersperse x zs@(y :. ys) = case ys of
  Nil -> zs
  _ :. _ -> y :. x :. intersperse x ys

concat :: Vect n (Vect k a) -> Vect (n * k) a
concat Nil = Nil
concat (xs :. xss) = xs ++ concat xss

concatMap :: (a -> Vect k b) -> Vect n a -> Vect (n * k) b
concatMap f = concat . map f

type family Intercalated (m :: PNat) (n :: PNat) (k :: PNat) :: PNat where
  Intercalated m Z k = Z
  Intercalated m (S Z) k = k
  Intercalated m (S n) k = k + m + Intercalated m n k

intercalate :: Vect m a -> Vect n (Vect k a) 
            -> Vect (Intercalated m n k) a
intercalate x Nil = Nil
intercalate x (y :. ys) = case ys of
  Nil -> y
  z :. zs -> y ++ x ++ intercalate x ys

zipWith :: (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zipWith f Nil Nil = Nil
zipWith f (x :. xs) (y :. ys) = f x y :. zipWith f xs ys

zip :: Vect n a -> Vect n b -> Vect n (a, b)
zip = zipWith (,)

unzip :: Vect n (a, b) -> (Vect n a, Vect n b)
unzip Nil = (Nil, Nil)
unzip ((x, y) :. zs) = case unzip zs of
  (xs, ys) -> (x :. xs, y :. ys)

newtype Swap f a b = Swap { unSwap :: f b a }

inSwap :: (f a b -> f x y) -> Swap f b a -> Swap f y x
inSwap f (Swap x) = Swap (f x)

replicate :: Natural pnat => pnat n -> a -> Vect n a
replicate n x = unSwap $ elimNat
  (Swap Nil)
  (\m -> Swap (x :. replicate m x))
  n

transpose :: Natural pnat => pnat n -> Vect m (Vect n a) -> Vect n (Vect m a)
transpose n Nil = replicate n Nil
transpose n (xs :. xss) = zipWith (:.) xs (transpose n xss)

permutations :: Vect n a -> Vect (Fact n) (Vect n a)
permutations Nil = Nil :. Nil
permutations (x :. xs) = concatMap (insert x) (permutations xs)

insert :: a -> Vect n a -> Vect (S n) (Vect (S n) a)
insert x Nil = (x :. Nil) :. Nil
insert x zs@(y :. ys) = (x :. zs) :. map (y :.) (insert x ys)

foldr :: (a -> b -> b) -> b -> Vect n a -> b
foldr f z Nil = z
foldr f z (x :. xs) = x `f` foldr f z xs

foldrN :: (forall m. a -> p m -> p (S m)) 
       -> p Z -> Vect n a -> p n
foldrN f z Nil = z
foldrN f z (x :. xs) = x `f` foldrN f z xs

newtype Splut f b a = Splut { unSplut :: (f a, b) }

splitAt :: forall a. forall k. forall n. forall pnat.
  Natural pnat => pnat n -> Vect (n + k) a -> (Vect n a, Vect k a)
splitAt i xs = case elimNat 
  (Splut (Swap Nil, xs) :: Splut (Swap Vect a) (Vect k a) Z)
  (\n -> case xs of 
    (x' :. xs') -> case splitAt n xs' of
      (ys, zs) -> Splut (Swap (x' :. ys), zs))
  i of
  Splut (Swap u, v) -> (u, v)

take :: (LTE n m ~ True, Natural pnat) => pnat n -> Vect m xs -> Vect n xs
take i xs = case elimNat 
  (Swap Nil)
  (\n -> case xs of (x' :. xs') -> Swap (x' :. take n xs'))
  i of
  Swap ys -> ys

newtype Const a b = Const a

drop :: Natural pnat => pnat n -> Vect (n + k) xs -> Vect k xs
drop i xs = case elimNat
  (Const xs)
  (\n -> case xs of (x' :. xs') -> Const (drop n xs'))
  i of
  Const ys -> ys

data SplitVects :: PNat -> * -> * where
  Split :: Vect m a -> Vect n a -> SplitVects (m + n) a

deriving instance Show a => Show (SplitVects n a)

partition :: (a -> Bool) -> Vect n a -> SplitVects n a
partition f Nil = Split Nil Nil
partition f (x :. xs) = case partition f xs of
  Split ys zs -> if f x 
    then Split (x :. ys) zs
    else gcastWith (plusSuccRightSucc ys zs) (Split ys (x :. zs))

splitUpon :: (a -> Bool) -> Vect n a -> SplitVects n a
splitUpon f Nil = Split Nil Nil
splitUpon f zs@(x :. xs) = if f x
  then Split Nil zs
  else case splitUpon f xs of
    Split as bs -> Split (x :. as) bs

(!!) :: Finite fin => Vect n a -> fin n -> a
(x :. xs) !! n = case elimFin (Const x) (\m -> Const (xs !! m)) n of
  Const y -> y

newtype Range fin n = Range (Vect n (fin n))

range :: (Natural snat, Finite fin) => snat n -> Vect n (fin n)
range n = case elimNat (Range Nil) (\i -> Range (F.zero :. map F.succ (range i))) n of
  Range y -> y

and, or :: Vect n Bool -> Bool
and = foldr (&&) True
or = foldr (||) False

minimum, maximum :: Ord a => Vect (S n) a -> a
minimum (x :. xs) = foldr min x xs
maximum (x :. xs) = foldr max x xs

sum, product :: Num a => Vect n a -> a
sum = foldr (+) 0
product = foldr (*) 1

findIndex :: Finite fin => (a -> Bool) -> Vect n a -> Maybe (fin n, a)
findIndex f Nil = Nothing
findIndex f (x :. xs) = if f x then Just (F.zero, x) 
  else fmap (\(i, z) -> (F.succ i, z)) (findIndex f xs)

generate :: (Natural snat, Finite fin) => snat n -> (fin n -> a) -> Vect n a
generate n f = case elimNat (Swap Nil)
  (\i -> Swap (f F.zero :. generate i (f . F.succ)))
  n of
  Swap y -> y
