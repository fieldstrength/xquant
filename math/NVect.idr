module NVect

import Control.Algebra
import Data.Vect

import math.NNat


%default total


||| Non-empty Vector
data NVect : NNat -> Type -> Type where
  vI : (x : a) -> NVect 1 a
  vS : (x : a) -> NVect (nS k) a -> NVect (nS $ S k) a

instance Functor (NVect n) where
  map f (vS x v) = vS (f x) $ map f v
  map f (vI x)   = vI $ f x  

zipWith : (a -> b -> c) -> NVect n a -> NVect n b -> NVect n c
zipWith f (vI x)   (vI y)   = vI $ f x y
zipWith f (vS x v) (vS y w) = vS (f x y) $ zipWith f v w

replicate : (n : NNat) -> (x : a) -> NVect n a
replicate (nS n) x = rep n x where
  rep : (n : Nat) -> (x : a) -> NVect (nS n) a
  rep Z     x = vI x
  rep (S n) x = vS x $ rep n x

fromVect : Vect (S n) a -> NVect (nS n) a
fromVect [x]        = vI x
fromVect (x::y::xs) = vS x $ fromVect (y::xs)

toVect : NVect (nS n) a -> Vect (S n) a
toVect (vI x)   = [x]
toVect (vS x v) = x :: (toVect v)

sum : Semigroup a => NVect n a -> a
sum (vI x)    = x
sum (vS x xs) = x <+> NVect.sum xs

product : Ring a => NVect n a -> a
product (vI x)    = x
product (vS x xs) = x <.> NVect.product xs

last : NVect n a -> a
last (vI x)   = x
last (vS x v) = last v

foldl1 : (a -> a -> a) -> NVect n a -> a
foldl1 f (vI x)     = x
foldl1 f (vS x v)   = f x $ foldl1 f v

%assert_total
foldr1 : (a -> a -> a) -> NVect n a -> a
foldr1 f (vI x)          = x
foldr1 f (vS y (vI x))   = f y x
foldr1 f (vS y (vS x v)) = foldr1 f (vS (f y x) v)

{- (++) : NVect n a -> NVect m a -> NVect (n+m) a
   (++) (vI x) w ?= vS x w -}
