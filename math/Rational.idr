module Rational

import Data.ZZ

import math.NNat


infixl 4 ~~


||| Sets identified under an equivalence relation (~~), defined by a 
||| projection (proj), satisfying the following properties:
|||
||| + Reflective:
|||     forall a,       a ~~ a = True
||| + Symmetric:
|||     forall a, b     a ~~ b = b ~~ a
||| + Transitive:
|||     forall a, b, c  (a ~~ b = True, b ~~ c = True) -> (a ~~ c = True)
class Eq a => Quotient a where
  proj : a -> a
  (~~) : Quotient a => a -> a -> Bool
  (~~) x y = (proj x) == (proj y)

class Quotient a => VerifiedQuotient a where
  projIdempotent : proj . proj = proj


%default total


||| Positive fraction, no simplification
data Fraction = Frac Nat NNat

instance Eq Fraction where
  (==) (Frac n m) (Frac a b) = (n == a) && (m == b)

simplify : Fraction -> Fraction
simplify (Frac n (nS d)) = Frac (div n $ gcd n (S d)) (toNNat $ div d $ gcd n (S d))

instance Quotient Fraction where
  proj = simplify

instance Ord Fraction where
  compare (Frac a (nS b)) (Frac c (nS d)) = compare (a * (S d)) (c * (S b))


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

instance Num Fraction where
  (+) = fplus
  (*) = fmult
  (-) x y = Frac 0 1
  abs = id
  fromInteger n = Frac (fromInteger n) 1


||| Rational number, from integer numerator and positive denominator
data Rational = rational ZZ NNat

instance Eq Rational where
  (==) (rational a b) (rational x y) = (a == x) && (b == y)

simp : Rational -> Rational
simp (rational (Pos  n) (nS d)) = let dd = S d in rational (Pos $ div n $ gcd n dd) (toNNat $ div dd $ gcd n dd)
simp (rational (NegS n) (nS d)) = 
  let dd = S d in 
  let m  = S n in 
    rational (NegS $ minus (div m $ gcd m dd) 1) (toNNat $ div dd $ gcd m dd)

instance Quotient Rational where
  proj = simp

instance Neg Rational where
  negate (rational z d) = rational (negate z) d


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
rminus x y = rplus x (-y)


instance Num Rational where
  (+) = rplus
  (-) = rminus
  (*) = rmult
  abs (rational z d) = rational (abs z) d
  fromInteger n = rational (fromInteger n) 1
