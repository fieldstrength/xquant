
module Alg

import Matrix


%default total


infix 6 :+

-- Simple Integer – bool for minus sign presence
data sInt = SInt Bool Nat

-- Complex Integer
data cInt = (:+) sInt sInt

-- equality and decidable equality for sInt, cInt
instance Eq sInt where
  (SInt b1 n1) == (SInt b2 n2) = (b1 == b2 && n1 == n2)

instance Eq cInt where
  (a :+ b) == (c :+ d) = (a == c && b == d)

instance Show sInt where
  show (SInt b n) = if b then "-" ++ (show n) else (show n)

instance Show cInt where
  show ((SInt br Z) :+ (SInt bi Z)) = "0"
  show ((SInt br n) :+ (SInt bi Z)) = show (SInt br n)
  show ((SInt br Z) :+ (SInt bi n)) = (if bi then "-i" else "i") ++ (if n == 1 then "" else show n)
  show ((SInt br n) :+ (SInt bi m)) = if bi then r ++ " - " ++ i else r ++ " + " ++ i where
    r : String
    r = show (SInt br n)
    i : String
    i = "i" ++ (if m == 1 then "" else show $ SInt False m)


-- Numeric operations and typeclass instances for sInt, cInt
%assert_total
sPlus : sInt -> sInt -> sInt
sPlus (SInt False n)      (SInt False m)      = SInt False (n + m)
sPlus (SInt True n)       (SInt True m)       = SInt True  (n + m)
sPlus (SInt _ Z)          s                   = s
sPlus s                   (SInt _ Z)          = s
sPlus (SInt False $ S n)  (SInt True  $ S m)  = SInt False n `sPlus` (SInt True m)
sPlus (SInt True  $ S n)  (SInt False $ S m)  = SInt True n  `sPlus` (SInt False m)

-- reverse sign
opp : sInt -> sInt
opp (SInt b n) = SInt (not b) n

-- Exclusive OR
xor : Bool -> Bool -> Bool
xor a b = if a then not b else b

sTimes : sInt -> sInt -> sInt
sTimes (SInt a x) (SInt b y) = SInt (xor a b) (x * y)

instance Num sInt where
  (+)            = sPlus
  (-) x y        = sPlus x $ opp y
  (*)            = sTimes
  abs (SInt b x) = (SInt False x)
  fromInteger i  = let n = abs i in let b = (i < 0) in SInt b (fromIntegerNat n)

instance Num cInt where
  (+) (a :+ b) (c :+ d) = (a+c) :+ (b+d)
  (-) (a :+ b) (c :+ d) = (a-c) :+ (b-d)
  (*) (a :+ b) (c :+ d) = (a*c-b*d) :+ (b*c+a*d)
  fromInteger x         = fromInteger x :+ 0
  abs (a :+ b)          = let s0 = SInt False Z in s0 :+ s0 -- magnitude not properly definable

instance Cast Nat cInt where
  cast n = (SInt False 0) :+ (SInt False n)



-- primative units for sInt, cInt
s1 : sInt
s1 = (SInt False 1)

sm1 : sInt
sm1 = (SInt True 1)

s0 : sInt
s0 = (SInt False 0)


C1 : cInt
C1 = s1 :+ s0

Ci : cInt
Ci = s0 :+ s1

Cm1 : cInt
Cm1 = sm1 :+ s0

Cmi : cInt
Cmi = s0 :+ sm1

C0 : cInt
C0 = s0 :+ s0

-------------------------------------------------------------------------------------------
--                                   Lie algebra stuff
-------------------------------------------------------------------------------------------


-- Lie algebra element GADT ~ one complex number for each algebra element
data Lie : Nat -> Type where
  lZ : Lie Z
  lS : cInt -> Lie k -> Lie (S k)

instance Eq (Lie n) where
  lZ == lZ                   = True
  (lS n $ l1) == (lS m $ l2) = n == m && l1 == l2

-- Easy initialize Lie element
lieI : Vect n cInt -> Lie n
lieI Nil       = lZ
lieI (c :: cs) = lS c $ lieI cs
