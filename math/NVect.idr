module NVect

import math.NNat

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