module Tensor

import Data.Vect
import Data.Fin
import Data.Matrix
import math.NNat


%default total


infixr 3 <||>

class Module a b => InnerProductSpace a b where
  (<||>) : b -> b -> a

instance RingWithUnity a => InnerProductSpace a (Vect n a) where
  (<||>) w v = foldr (<+>) neutral (zipWith (<.>) w v)


||| A general tensor of arbitrary index structure
data Tensor : Vect n NNat -> Type -> Type where
  Scalr : a -> Tensor [] a
  Tensr : Vect (S n) (Tensor w a) -> Tensor (nS n :: w) a


||| Homogeneous tensor with all indices of the same kind but arbitrary rank
data HTensor : Nat -> NNat -> Type -> Type where
  hZ : a -> HTensor Z n a
  hS : Vect (S n) (HTensor m (nS n) a) -> HTensor (S m) (nS n) a


||| Signature for individual tensor indices: an index size and specification of how many components are timelike
data TSig : Type where
  MkSig : (n : NNat) -> Fin (S $ nnToNat n) -> TSig

||| Spacetime tensor, arbitrary index structure and possibly timelike dimensions
data STensor : Vect n TSig -> Type -> Type where
  sZ : a -> STensor [] a
  sT : (h : TSig) -> Vect (S n) (STensor v a) -> STensor (h :: v) a


tzip : (f : a -> b -> c) -> Tensor v a -> Tensor v b -> Tensor v c
tzip f (Scalr x) (Scalr y) = Scalr $ f x y
tzip f (Tensr v) (Tensr w) = Tensr $ zipWith (tzip f) v w


trep : (v : Vect n NNat) -> a -> Tensor v a
trep Nil          x = Scalr x
trep (nS n :: ns) x = Tensr $ replicate (S n) $ trep ns x


instance Functor (Tensor v) where
  map f (Scalr x) = Scalr $ f x
  map f (Tensr v) = Tensr $ map (map f) v

instance Semigroup a => Semigroup (Tensor v a) where
  (<+>) v w = tzip (<+>) v w

instance Monoid a => Monoid (Tensor v a) where
  neutral {v} = trep v neutral

instance Group a => Group (Tensor v a) where
  inverse = map inverse

instance AbelianGroup a => AbelianGroup (Tensor v a) where {}

instance Ring a => Ring (Tensor v a) where
  (<.>) v w = tzip (<.>) v w

instance RingWithUnity a => RingWithUnity (Tensor v a) where
  unity {v} = trep v unity

instance Field a => Field (Tensor v a) where
  inverseM = map inverseM

instance RingWithUnity a => Module a (Tensor v a) where
  (<#>) r v = map (r <.>) v
