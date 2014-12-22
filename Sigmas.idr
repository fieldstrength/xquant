
module Sigmas


infixr 5 <>
infixr 7 <&>

-------------------------------------------------------------------------------------------
--           Data for Sigma Operators  • Complex signs (Phases)
--                                     • Pauli operators
--                                     • Higher Sigma operators 
--                                        (tensor products of Paulis with an overall phase)
-------------------------------------------------------------------------------------------

||| 4 primative complex phases, (+1), (+i), (-1), (-i),
||| bools represent minus sign and i presence respectively
data Phase : Type where
  Sign : (minus : Bool) -> (i : Bool) -> Phase

instance Show Phase where
  show (Sign False False) = "+1"
  show (Sign False True)  = "+i"
  show (Sign True False)  = "-1"
  show (Sign True True)   = "-i"

instance Eq Phase where
  (==) (Sign m1 i1) (Sign m2 i2) = (m1 == m2) && (i1 == i2)
  

-- Exclusive OR
xor : Bool -> Bool -> Bool
xor a b = if a then not b else b

instance Semigroup Phase where
  (<+>) (Sign as ai) (Sign bs bi) = Sign (xor (ai && bi) $ xor as bs) (xor ai bi)

instance Monoid Phase where
  neutral = Sign False False

instance Group Phase where
  inverse (Sign a b) = Sign (xor a b) b
  
star : Phase -> Phase
star (Sign a b) = Sign a (not b)

-- Phase Shorthands - Capital 'P' for phases
P1 : Phase
P1 = Sign False False
Pi : Phase
Pi = Sign False True
M1 : Phase
M1 = Sign True False
Mi : Phase
Mi = Sign True True 


-- Pauli Data – Capital 'S' for basic sigma operators
data Pauli = SI | SX | SY | SZ

instance Show Pauli where 
  show SI = "I"
  show SX = "x"
  show SY = "y"
  show SZ = "z" -- should be "σz" whene idris can print non-8-bit characters

instance Eq Pauli where
  SI == SI = True
  SX == SX = True
  SY == SY = True
  SZ == SZ = True
  _  == _  = False

class LaTeX a where
  TeX : a -> String

instance LaTeX Pauli where
  TeX SI = "\\mathbb{I}"
  TeX SX = "\\sigma_x"
  TeX SY = "\\sigma_y"
  TeX SZ = "\\sigma_z"
  
  
-- Higher Sigma operator datatype, indexed by Nat
data Sigma : Nat -> Type where
  sPhase : Phase -> Sigma Z
  Sig    : Pauli -> Sigma k -> Sigma (S k)


-- LaTeX printing, generic show for higher Sigmas
instance LaTeX (Sigma n) where
  TeX (sPhase $ Sign a b) = (if a then "-" else "") ++ (if b then "i" else "1")
  TeX s                   = (Prefix s) ++ (suffix s) where
    suffix : Sigma n -> String
    suffix (sPhase ph)         = ""
    suffix (Sig p (sPhase ph)) = TeX p
    suffix (Sig p s)           = (TeX p) ++ " \\otimes " ++ (suffix s)
    Prefix : Sigma n -> String
    Prefix (sPhase (Sign a b)) = (if a then "-" else "") ++ (if b then "i " else " ")
    Prefix (Sig p s)           = Prefix s

instance Show (Sigma n) where
  show (sPhase phase) = show phase
  show s = (Prefix s) ++ "[" ++ (suffix s) ++ "]" where
    suffix : Sigma n -> String
    suffix (sPhase ph)         = ""
    suffix (Sig p (sPhase ph)) = (show p)
    suffix (Sig p s)           = (show p) ++ (suffix s)
    Prefix : Sigma n -> String
    Prefix (sPhase (Sign a b)) = (if a then "-" else "") ++ (if b then "i " else "")
    Prefix (Sig p s)           = Prefix s


-- 4 Standard Sigma 1s
sX : (Sigma 1)
sX = Sig SX $ sPhase P1

sY : Sigma 1
sY = Sig SY $ sPhase P1

sZ : Sigma 1
sZ = Sig SZ $ sPhase P1

sI : Sigma 1
sI = Sig SI $ sPhase P1


-------------------------------------------------------------------------------------------
--           Operations with Sigmas   • Helper functions: getPhase, topPauli, lastPauli, pack
--                                    • Scalar multiply 
--                                    • (Single) Sigma multiply
--                                    • (Higher) Sigma multiply
-------------------------------------------------------------------------------------------

-- Extract the Phase, first Pauli or last Pauli from a Sigma
getPhase : Sigma n -> Phase
getPhase (sPhase p) = p
getPhase (Sig p s)  = getPhase s

topPauli : Sigma (S k) -> Pauli
topPauli (Sig p s) = p

lastPauli : Sigma (S k) -> Pauli
lastPauli (Sig pl (sPhase ph)) = pl
lastPauli (Sig pl (Sig pl2 s)) = lastPauli (Sig pl2 s)

-- Pack a Pauli into a Sigma
pack : Pauli -> Sigma 1
pack s = Sig s $ sPhase P1


-- Phase times a Sigma
xPhaseSig.(*) : Phase -> Sigma n -> Sigma n
xPhaseSig.(*) ph (sPhase ph2) = sPhase $ ph <+> ph2
xPhaseSig.(*) ph (Sig pl s)   = Sig pl $ ph * s

xSigPhase.(*) : Sigma n -> Phase -> Sigma n
xSigPhase.(*) s p = p * s

-- Single Sigma multiply
s1Mult : Sigma 1 -> Sigma 1 -> Sigma 1
s1Mult (Sig x1 $ sPhase p1) (Sig x2 $ sPhase p2) = case x1 of
                                                        SX => case x2 of
                                                                   SX => Sig SI (sPhase $ p1 <+> p2) 
                                                                   SY => Sig SZ (sPhase $ p1 <+> p2 <+> Pi)
                                                                   SZ => Sig SY (sPhase $ p1 <+> p2 <+> Mi)
                                                                   SI => Sig SX (sPhase $ p1 <+> p2)
                                                        SY => case x2 of
                                                                   SY => Sig SI (sPhase $ p1 <+> p2)
                                                                   SZ => Sig SX (sPhase $ p1 <+> p2 <+> Pi)
                                                                   SX => Sig SZ (sPhase $ p1 <+> p2 <+> Mi)
                                                                   SI => Sig SY (sPhase $ p1 <+> p2)
                                                        SZ => case x2 of
                                                                   SZ => Sig SI (sPhase $ p1 <+> p2)
                                                                   SX => Sig SY (sPhase $ p1 <+> p2 <+> Pi)
                                                                   SY => Sig SX (sPhase $ p1 <+> p2 <+> Mi)
                                                                   SI => Sig SZ (sPhase $ p1 <+> p2)
                                                        SI => case x2 of
                                                                   SI => Sig SI (sPhase $ p1 <+> p2)
                                                                   SX => Sig SX (sPhase $ p1 <+> p2)
                                                                   SY => Sig SY (sPhase $ p1 <+> p2)
                                                                   SZ => Sig SZ (sPhase $ p1 <+> p2)


-- Higher Sigma mutiply
sMult : Sigma n -> Sigma n -> Sigma n
sMult (sPhase p1)  (sPhase p2)  = sPhase $ p1 <+> p2
sMult (Sig pl1 s1) (Sig pl2 s2) with (s1Mult (pack pl1) (pack pl2)) 
  | r = Sig (topPauli r) ((getPhase r) * (sMult s1 s2))
  
-- Infix op for Sigma multiply
(<>) : Sigma n -> Sigma n -> Sigma n
(<>) = sMult


-- Tensor multiply Sigmas ('otimes', i.e. ⊗ )
ox : Sigma n -> Sigma m -> Sigma (n + m)
ox s            (sPhase p)   ?= {Sigma_OTimes_Lemma_1} p * s
ox (sPhase p)   s             = p * s
ox (Sig pl1 s1) (Sig pl2 s2) ?= {Sigma_OTimes_Lemma_2} ox (dropLast $ Sig pl1 s1)
                                                          (Sig (lastPauli $ Sig pl1 s1) (Sig pl2 s2)) where
  dropLast : {k : Nat} -> Sigma (S k) -> Sigma k
  dropLast (Sig pl (sPhase ph)) = (sPhase ph)
  dropLast (Sig pl (Sig pl2 s)) = Sig pl (dropLast (Sig pl2 s))

-- Infix tensor multiply Sigmas
(<&>) : Sigma n -> Sigma m -> Sigma (n + m)
(<&>) = ox

-- Tensor powers of a Sigma op
opower : Sigma n -> (m : Nat) -> Sigma (n * m)
opower s Z     ?=  {Sigma_Power_Lemma_1}  sPhase P1
opower s (S n) ?=  {Sigma_Power_Lemma_2}  s <&> (opower s n)



---------- Proofs ----------

Sigma_OTimes_Lemma_1 = proof
  intro
  rewrite (plusZeroRightNeutral n)
  intros
  trivial

Sigma_OTimes_Lemma_2 = proof
  intros
  rewrite sym $ plusSuccRightSucc k (S k1)
  trivial



Sigma_Power_Lemma_1 = proof
  intros
  rewrite (sym $ multZeroRightZero n)
  trivial

Sigma_Power_Lemma_2 = proof
  intros
  rewrite (sym $ multRightSuccPlus n n1)
  trivial

