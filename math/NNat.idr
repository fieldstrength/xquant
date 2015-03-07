module NNat

import Data.ZZ
import Data.Fin


%default total


||| Non-zero natural number
data NNat = nS Nat

||| Add non-zero natural numbers
nPlus : NNat -> NNat -> NNat
nPlus (nS n) (nS m) = nS $ S (n + m)

||| Multiply non-zero natrual numbers
nMult : NNat -> NNat -> NNat
nMult (nS x) (nS y) with ((S x) * (S y))
  | (S r) = nS r
  | Z     = nS Z -- for totality check only

||| Subtract non-zero natural numbers. If the second number
||| is larger than the first, returns 1
nMinus : NNat -> NNat -> NNat
nMinus (nS Z)     _          = nS Z
nMinus (nS $ S x) (nS Z)     = nS x
nMinus (nS $ S x) (nS $ S y) = nS $ x - (S y)

instance Num NNat where
  (+) = nPlus
  (-) = nMinus
  (*) = nMult
  abs = id
  fromInteger 0 = nS Z
  fromInteger n = nS (fromInteger $ n - 1)

nnToNat : NNat -> Nat
nnToNat (nS n) = S n

||| Destructively convert Nat to NNat
toNNat : Nat -> NNat
toNNat Z     = nS Z
toNNat (S Z) = nS Z
toNNat (S k) = 1 + (toNNat k)

finType : NNat -> Type
finType (nS n) = Fin (S $ S n)


instance Cast NNat Nat where
  cast = nnToNat

instance Cast NNat Integer where
  cast = cast . nnToNat

instance Cast NNat Int where
  cast = cast . nnToNat

instance Cast NNat ZZ where
  cast (nS n) = Pos (S n)

instance Cast String Nat where
  cast = fromInteger . cast {to=Integer}

instance Cast String NNat where
  cast = toNNat . cast {to=Nat}

instance Eq NNat where
  (nS x) == (nS y) = x == y

instance Ord NNat where
  compare (nS x) (nS y) = compare x y

instance Show NNat where
  show (nS n) = show (S n)
