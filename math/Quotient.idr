module Quotient


%default total


infixl 4 ~~
infixl 4 ~=


||| Sets identified under an equivalence relation defined by a
||| projection (proj), thus inhereting the reflective, symmetric and
||| transitive properties of equality. The projection must be idempotent:
|||
||| proj . proj = proj
|||
class Quotient a where
  proj : a -> a

||| Equality test under quotient projection
(~~) : (Eq a, Quotient a) => a -> a -> Bool
(~~) x y = (proj x) == (proj y)

class Quotient a => VerifiedQuotient a where
  projIdempotent : proj . proj = proj


---- Quotient counterpart to the (=) data type ----

data (~=) : (x,y : a) -> Type where
  QRefl : Quotient a => (x,y : a) -> (prf : proj x = (proj y)) -> x ~= y


{-  With this we get an unexpected type class problem:

*math/Rational> QRefl f1 f2 Refl
Can't resolve type class Quotient Fraction

    Even though:

*math/Rational> f1 ~~ f2
True : Bool
*math/Rational> QRefl f1 f2
QRefl (Frac 6 (nS 2)) (Frac 4 (nS 1)) : (Frac 2 (nS 0) =
                                         Frac 2 (nS 0)) ->
                                        Frac 6 (nS 2) ~= Frac 4 (nS 1)

    Ideally, we'd really like to simply do:

data (~=) : Quotient a => (x,y : a) -> Type where
  QRefl : Quotient a => {x,y : a} -> {auto prf : proj x = (proj y)} -> x ~= y

    This previously has resulted in "Can't solve goal". -}
