module Rational

import math.Hilbert

infixl 4 ~~
infixl 4 ~
infixr 5 //

data Fraction = Frac Nat Nat

simplify : Fraction -> Fraction
simplify (Frac n d) = Frac (div n $ gcd n d) (div d $ gcd n d)

instance Eq Fraction where
  (==) (Frac n m) (Frac a b) = (n == a) && (m == b)

class Eq a => Quotient a where
  proj : a -> a

(~~) : Quotient a => a -> a -> Bool
(~~) x y = (proj x) == (proj y)

class Quotient a => VerifiedQuotient a where
  projIdempotent : proj . proj = proj

instance Quotient Fraction where
  proj = simplify
