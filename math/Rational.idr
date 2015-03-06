module Rational

import Data.ZZ

import math.NNat


%default total


||| Sets identified under an equivalence relation defined by a
||| projection (proj), thus inhereting the reflective, symmetric and
||| transitive properties of equality. The projection must be idempotent:
|||
||| + proj . proj = proj
|||
class Eq a => Quotient a where
  proj : a -> a

infixl 4 ~~

||| Equality test under quotient projection
(~~) : (Eq a, Quotient a) => a -> a -> Bool
(~~) x y = (proj x) == (proj y)

class Quotient a => VerifiedQuotient a where
  projIdempotent : proj . proj = proj


-----------------------------------------------------------------------
--                         Positive Rationals
-----------------------------------------------------------------------

||| Positive fraction, no simplification
data Fraction = Frac Nat NNat

simplify : Fraction -> Fraction
simplify (Frac n (nS d)) = Frac (div n $ gcd n (S d)) (toNNat $ div d $ gcd n (S d))

num : Fraction -> Nat
num (Frac n d) = n

denom : Fraction -> NNat
denom (Frac n d) = d

fmult : Fraction -> Fraction -> Fraction
fmult (Frac n1 d1) (Frac n2 d2) = Frac (n1*n2) (d1*d2)

fplus : Fraction -> Fraction -> Fraction
fplus (Frac n1 d1) (Frac n2 d2) = case (d1==d2) of
                                       True  => Frac (n1 + n2) d1
                                       False => Frac ((cast d2 * n1) + (cast d1 * n2)) (d1*d2)

instance Eq Fraction where
  (==) (Frac n m) (Frac a b) = (n == a) && (m == b)

instance Quotient Fraction where
  proj = simplify

instance Ord Fraction where
  compare (Frac a (nS b)) (Frac c (nS d)) = compare (a * (S d)) (c * (S b))

instance Num Fraction where
  (+) = fplus
  (*) = fmult
  (-) x y = Frac 0 1
  abs = id
  fromInteger n = Frac (fromInteger n) 1


-----------------------------------------------------------------------
--                            Rationals
-----------------------------------------------------------------------


||| Rational number constructed from integer numerator, positive denominator
data Rational = rational ZZ NNat


simp : Rational -> Rational
simp (rational (Pos  n) (nS d)) = let dd = S d in rational (Pos $ div n $ gcd n dd) (toNNat $ div dd $ gcd n dd)
simp (rational (NegS n) (nS d)) = 
  let dd = S d in 
  let nn = S n in 
    rational (NegS $ minus (div nn $ gcd nn dd) 1) (toNNat $ div dd $ gcd nn dd)

numerator : Rational -> ZZ
numerator (rational z n) = z

denominator : Rational -> NNat
denominator (rational z n) = n

rmult : Rational -> Rational -> Rational
rmult (rational z1 d1) (rational z2 d2) = rational (z1*z2) (d1*d2)

rplus : Rational -> Rational -> Rational
rplus (rational z1 d1) (rational z2 d2) = case (d1==d2) of
                                               True  => rational (z1 + z2) d1
                                               False => rational ((cast d2 * z1) + (cast d1 * z2)) (d1 * d2)

rminus : Rational -> Rational -> Rational
rminus x (rational z d) = rplus x (rational (negate z) d)


instance Eq Rational where
  (==) (rational a b) (rational x y) = (a == x) && (b == y)

instance Quotient Rational where
  proj = simp

instance Neg Rational where
  negate (rational z d) = rational (negate z) d

instance Num Rational where
  (+) = rplus
  (-) = rminus
  (*) = rmult
  abs (rational z d) = rational (abs z) d
  fromInteger n = rational (fromInteger n) 1

instance Semigroup Rational where
  (<+>) = (+)

instance Monoid Rational where
  neutral = 0

instance Group Rational where
  inverse = negate

instance AbelianGroup Rational where {}

instance Ring Rational where
  (<.>) = (*)

instance RingWithUnity Rational where
  unity = 1


---- two fractions for testing ----

f1 : Fraction
f1 = Frac 6 3

f2 : Fraction
f2 = Frac 4 2


-----------------------------------------------------------------------
--            A Quotient counterpart to the (=) data type
-----------------------------------------------------------------------

infixl 4 ~=
data (~=) : Quotient a => (x,y : a) -> Type where
  QRefl : Quotient a => (x,y : a) -> (prf : proj x = (proj y)) -> x ~= y
 
 
{-  With this we get an unexpected type class problem:

*math/Rational> QRefl f1 f2 Refl
Can't resolve type class Quotient Fraction 

    Even though:

*math/Rational> QRefl f1 f2
QRefl (Frac 6 (nS 2)) (Frac 4 (nS 1)) : (Frac 2 (nS 0) =
                                         Frac 2 (nS 0)) ->
                                        Frac 6 (nS 2) ~= Frac 4 (nS 1)

    Ideally, we'd really like to simply do:

data (~=) : Quotient a => (x,y : a) -> Type where
  QRefl : Quotient a => {x,y : a} -> {auto prf : proj x = (proj y)} -> x ~= y 

    This previously has resulted in "Can't solve goal". -}
