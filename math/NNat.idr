module NNat


||| Non-zero natural number
data NNat = One | S NNat

nPlus : NNat -> NNat -> NNat
nPlus One   x = S x
nPlus (S x) y = nPlus x (S y)

nMult : NNat -> NNat -> NNat
nMult One   x = x
nMult (S x) y = nPlus y $ nMult x y

nMinus : NNat -> NNat -> NNat
nMinus (S x) (S y) = nMinus x y
nMinus (S x) One   = x
nMinus One   _     = One

instance Cast Nat NNat where
  cast Z     = One
  cast (S Z) = One
  cast (S n) = S $ cast n

nnToNat : NNat -> Nat
nnToNat One   = S Z
nnToNat (S n) = S $ nnToNat n

instance Cast NNat Nat where
  cast = nnToNat

instance Num NNat where
  (+) = nPlus
  (-) = nMinus
  (*) = nMult
  abs = id
  fromInteger 1 = One
  fromInteger n = cast {to=NNat} $ cast {to=Nat} n

band : Bool -> Bool -> Bool
band True True = True
band _    _    = False

xor : Bool -> Bool -> Bool
xor False b = b
xor True  b = not b


instance Semigroup Bool where
  (<+>) = xor

instance Monoid Bool where
  neutral = False

instance Group Bool where
  inverse = (xor True)
  
instance AbelianGroup Bool

instance Ring Bool where 
  (<*>) = (band)
 
instance RingWithUnity Bool where
  unity = True
