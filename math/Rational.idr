module Rational

import Data.ZZ
import math.Hilbert
import math.NNat

infixl 4 ~~

class Eq a => Quotient a where
  proj : a -> a
  (~~) : Quotient a => a -> a -> Bool
  (~~) x y = (proj x) == (proj y)

class Quotient a => VerifiedQuotient a where
  projIdempotent : proj . proj = proj


||| Positive fraction, no simplification
data Fraction = Frac Nat NNat

instance Eq Fraction where
  (==) (Frac n m) (Frac a b) = (n == a) && (m == b)

total
simplify : Fraction -> Fraction
simplify (Frac n (nS d)) = Frac (div n $ gcd n (S d)) (toNNat $ div d $ gcd n (S d))

instance Quotient Fraction where
  proj = simplify

instance Ord Fraction where
  compare (Frac a (nS b)) (Frac c (nS d)) = compare (a * (S d)) (c * (S b))


||| Rational number, from integer numerator and positive denominator
data Rational = rational ZZ NNat

instance Eq Rational where
  (==) (rational a b) (rational x y) = (a == x) && (b == y)

total
simp : Rational -> Rational
simp (rational (Pos  n) (nS d)) = let dd = S d in rational (Pos $ div n $ gcd n dd) (toNNat $ div dd $ gcd n dd)
simp (rational (NegS n) (nS d)) = 
  let dd = S d in 
  let m  = S n in 
    rational (NegS $ minus (div m $ gcd m dd) 1) (toNNat $ div dd $ gcd m dd)

instance Quotient Rational where
  proj = simp

numerator : Rational -> ZZ
numerator (rational z n) = z

denominator : Rational -> NNat
denominator (rational z n) = n
