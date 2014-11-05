module Rational

infixl 4 ~~
infixl 4 ~

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

data Equivalent : Quotient a => (x,y : a) -> Type where
  (~) : Quotient a => (x,y : a) -> (proj x) = (proj y) -> Equivalent x y



{- infixl 4 =#=    -- Γλ

data Ratio = MkRatio Nat Nat

simplify : Ratio -> Ratio
simplify (MkRatio n d) = MkRatio (div n $ gcd n d) (div d $ gcd n d)

class Quotient a where
  project : a -> a
  (=#=)   : a -> a -> Bool  -- 'superficial equality'

instance Quotient a => Eq a where
  (==) x y = (project x) =#= (project y)
  
instance Quotient Ratio where
  project = simplify
  (=#=) (MkRatio n m) (MkRatio x y) = (n == x) && (m == y)
 
class Quotient a => VerifiedQuotient a where
  projectIdempotent : project . project = project


*Rational> :r
Type checking ./Rational.idr
./Rational.idr:14:10:
Overlapping instance: Eq Int already defined


infixl 4 ~==

data Fraction = Frac Nat Nat

simplify : Fraction -> Fraction
simplify (Frac n d) = Frac (div n $ gcd n d) (div d $ gcd n d)

class Eq a => Quotient a b where
  project : a -> a

class Quotient a b => Eq b where
  (==) x y = 

instance Quotient Ratio where
  project = simplify
  (~==) (MkRatio n m) (MkRatio x y) = (n == x) && (m == y)

instance Quotient a => Eq a where
  (==) x y = (project x) ~== (project y)
 
class Quotient a => VerifiedQuotient a where
  projectIdempotent : project . project = project


Type checking ./Rational.idr
./Rational.idr:18:10:
Overlapping instance: Eq Int already defined
-}