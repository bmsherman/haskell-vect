{-# LANGUAGE DataKinds, KindSignatures, GADTs, TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.VectI where

import Data.SFin
import Data.SNat

import Data.Coerce (coerce)
import qualified Data.List as L
import Data.Proxy (Proxy (..))
import Data.Type.Equality ((:~:) (Refl), gcastWith)
import GHC.TypeLits
import qualified Prelude as P
import Prelude (Show (show), (.), Bool (..), undefined, Maybe (..), ($)
       , Functor (fmap), Eq (..), Ord (..), Ordering (..), Num (..)
       , (&&), (||), max, min)
import Unsafe.Coerce (unsafeCoerce)

newtype Vect :: Nat -> * -> * where
  MkVect :: [a] -> Vect n a
  deriving (Eq, Show, Ord)

instance Functor (Vect n) where
  fmap f = coerce (P.map f)

nil :: Vect 0 a
nil = MkVect []

cons :: a -> Vect n a -> Vect (1 + n) a
cons x (MkVect xs) = MkVect (x : xs)

toList :: Vect n a -> [a]
toList (MkVect xs) = xs

(++) :: Vect m a -> Vect n a -> Vect (m + n) a
MkVect xs ++ MkVect ys = coerce (xs P.++ ys)

head :: Vect (1 + n) a -> a
head (MkVect xs) = P.head xs

last :: Vect (1 + n) a -> a
last (MkVect xs) = coerce (P.last xs)

tail :: Vect (1 + n) a -> Vect n a
tail (MkVect xs) = coerce (P.tail xs)

init :: Vect (1 + n) a -> Vect n a
init (MkVect xs) = coerce (P.init xs)

null :: Vect n a -> Bool
null (MkVect xs) = P.null xs

length :: Vect n a -> SNat n
length (MkVect xs) = unsafeMkSNat (P.length xs)

map :: (a -> b) -> Vect n a -> Vect n b
map f (MkVect xs) = coerce (P.map f xs)

nPlusZIsN :: Vect n a -> Vect n a :~: Vect (n + 0) a
nPlusZIsN _ = Refl

plusSuccRightSucc :: Vect n a -> Vect m a
  -> Vect (1 + (n + m)) a :~: Vect (n + (1 + m)) a
plusSuccRightSucc _ _ = unsafeCoerce Refl

unsafeCastWith :: (a :~: b) -> ((a ~ b) => r) -> r
unsafeCastWith _ = unsafeCoerce

reverse :: Vect n a -> Vect n a
reverse (MkVect zs) = coerce (P.reverse zs)

type family Interspersed (n :: Nat) :: Nat where
  Interspersed 0 = 0
  Interspersed 1 = 1
  Interspersed n = 2 + (Interspersed (n - 1))

intersperse :: a -> Vect n a -> Vect (Interspersed n) a
intersperse x (MkVect xs) = MkVect (L.intersperse x xs)

concat :: Vect n (Vect k a) -> Vect (n * k) a
concat (MkVect xs) = MkVect (P.concat (coerce xs))

concatMap :: (a -> Vect k b) -> Vect n a -> Vect (n * k) b
concatMap f = concat . map f

type family Intercalated (m :: Nat) (n :: Nat) (k :: Nat) :: Nat where
  Intercalated m 0 k = 0
  Intercalated m 1 k = k
  Intercalated m n k = k + m + Intercalated m (n - 1) k

intercalate :: Vect m a -> Vect n (Vect k a) 
            -> Vect (Intercalated m n k) a
intercalate (MkVect x) (MkVect xs) = MkVect (L.intercalate x (coerce xs))

zipWith :: (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zipWith f (MkVect xs) (MkVect ys) = MkVect (P.zipWith f xs ys)

zip :: Vect n a -> Vect n b -> Vect n (a, b)
zip = zipWith (,)

unzip :: Vect n (a, b) -> (Vect n a, Vect n b)
unzip (MkVect zs) = case P.unzip zs of
  (xs, ys) -> (MkVect xs, MkVect ys)
  
replicate :: SNat n -> a -> Vect n a
replicate n x = MkVect (P.replicate (snat n) x)

transpose :: SNat n -> Vect m (Vect n a) -> Vect n (Vect m a)
transpose n (MkVect []) = replicate n (MkVect [])
transpose n (MkVect (xs : xss)) = coerce (
  zipWith cons xs (transpose n (MkVect xss)))

type family Fact (n :: Nat) :: Nat where
  Fact 0 = 1
  Fact n = n * (Fact (n - 1))

permutations :: Vect n a -> Vect (Fact n) (Vect n a)
permutations (MkVect xs) = coerce (L.permutations xs)

foldr :: (a -> b -> b) -> b -> Vect n a -> b
foldr f z (MkVect xs) = P.foldr f z xs

splitAt :: SNat n -> Proxy k -> Vect (n + k) a -> (Vect n a, Vect k a)
splitAt n _ (MkVect xs) = case P.splitAt (snat n) xs of
  (ys, zs) -> (MkVect ys, MkVect zs)

take :: SNat n -> Proxy k -> Vect (n + k) xs -> Vect n xs
take n _ (MkVect xs) = MkVect (P.take (snat n) xs)

drop :: SNat n -> Proxy k -> Vect (n + k) xs -> Vect k xs
drop n _ (MkVect xs) = MkVect (P.drop (snat n) xs)

data SplitVects :: Nat -> * -> * where
  Split :: Vect m a -> Vect n a -> SplitVects (m + n) a

deriving instance Show a => Show (SplitVects n a)

partition :: (a -> Bool) -> Vect n a -> SplitVects n a
partition f (MkVect xs) = case L.partition f xs of
  (ys, zs) -> unsafeCoerce (Split (MkVect ys) (MkVect zs))

splitUpon :: (a -> Bool) -> Vect n a -> SplitVects n a
splitUpon f (MkVect []) = unsafeCoerce (Split (MkVect []) (MkVect []))
splitUpon f zs@(MkVect (x : xs)) = if f x
  then Split nil zs
  else case splitUpon f (MkVect xs) of
    Split as bs -> unsafeCoerce (Split (x `cons` as) bs)

(!!) :: Vect n a -> Fin n -> a
MkVect xs !! n = xs P.!! finToInt n

and, or :: Vect n Bool -> Bool
and = foldr (&&) True
or = foldr (||) False

minimum, maximum :: Ord a => Vect (1 + n) a -> a
minimum (MkVect xs) = P.minimum xs
maximum (MkVect xs) = P.maximum xs

sum, product :: Num a => Vect n a -> a
sum = foldr (+) 0
product = foldr (*) 1

{-
findIndex :: (a -> Bool) -> Vect n a -> Maybe (Fin n, a)
findIndex f Nil = Nothing
findIndex f (x :. xs) = if f x then Just (FZ, x) 
  else fmap (\(i, z) -> (FS i, z)) (findIndex f xs)
-}

test :: Vect (Fact 6) (Vect 6 P.Int)
test = permutations (cons 1 (cons 2 (cons 3 (cons 4 (cons 5 (cons 6 nil))))))
