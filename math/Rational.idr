module Rational

data Ratio : Nat -> Nat -> Type where
  MkRatio : (n : Nat) -> (d : Nat) -> let g = gcd n d in Ratio (n `div` g) (d `div` g)

class Quotient a where
  project : a -> a

class Quotient a => VerifiedQuotient a where
  projectIdempotent : project . project = project

data Quot : a -> (a -> a) -> Type where
  MkQuot : (x : a) -> (f : a -> a) -> Quot x f

data Idempotence : (a -> a) -> Type where
  MkIdem : (f : a -> a) -> (f . f = f) -> Idempotence f

data VerifiedQuot : a -> (a -> a) -> Type where
  MkVerQuot : (x : a) -> (f : a -> a) -> VerifiedQuot (f x) f

instance Eq Ratio where
  (MkRatio n m) == (MkRatio x y) = (n == x) && (m == y)
