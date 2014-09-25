
module Gamma

import Quantum
import Alg


-- Begin with two primative Gamma matrices, Γ0 and Γ1
-- Defining them as both Floating point and symbolic matrices

-- Γ0 = iσy
Gamma0 : QubitObs 1
Gamma0 = [[c0, cm1], [c1, c0]]

Γ0 : Matrix 2 2 cInt
Γ0 = [[C0, Cm1], [C1, C0]]

-- Γ1 = σx
Gamma1 : QubitObs 1
Gamma1 = [[c0, c1], [c1, c0]]

Γ1 : Matrix 2 2 cInt
Γ1 = [[C0, C1], [C1, C0]]

-- Construct gammas of even dimensional representations (D = 2k + 2) by tensoring as follows:

--    Gamma^μ    = gamma^mu <&> diag(-1,1)    or equivalently;
--    Gamma^μ    = gamma^mu <&> (Gamma1 <> Gamma0)  (where mu <- [0..D-2] )
--
--    Gamma^{D-1} = Id <&> Γ1    = Id <&> σx 
--
--    Gamma^D     = Id <&> -iΓ0  = Id <&> σy
--
-- All gammas defined in this way satisy the fundamental relation:

--   {Γμ,Γν} = 2 η{μν} Id   (upstairs indices)

-- They also furnish Poincaré generators faithfully satisfying: i[Σμν,Σσρ] = ηνσΣμρ + ημρΣνσ − ηνρΣμσ − ημσΣνρ 
--   where Σ^{μν} = −i[Γ^μ,Γ^ν]
-- This holds in any dimensionality and in both Minkowski and Euclidean signatures.

-- Set of Gamma matrices for even dimension D = 2k + 2, with size 2^(k+1) 
gammaSetEven : (k : Nat) -> Vect (k*2+2) $ Matrix (power 2 $ S k) (power 2 $ S k) (Complex Float)
gammaSetEven Z      = [Gamma0, Gamma1]
gammaSetEven (S k) ?= {Gamma_Lemma} map (\g => g <&> (Gamma1 <> Gamma0)) (gammaSetEven k) 
  ++ [idN (power 2 $ S k) <&> Gamma1, idN (power 2 $ S k) <&> (mScale cmi Gamma0)]
  
ΓsetEven : (k : Nat) -> Vect (k*2+2) $ Matrix (power 2 $ S k) (power 2 $ S k) cInt
ΓsetEven Z      = [Γ0, Γ1]
ΓsetEven (S k) ?= {Γ_Lemma} map (\g => g <&> (Γ1 <> Γ0)) (ΓsetEven k) 
  ++ [idN (power 2 $ S k) <&> Γ1, idN (power 2 $ S k) <&> (mScale Cmi Γ0)]

-- Now define the "5th Gamma matrix"
--   Γ = i^{-k} (Γ^0 ... Γ^{D-1})
-- It has eigenvalues of ±1 and satisfies
--   Γ^2 = 1
--   {Γ,Γ^μ} = 0
--   [Γ,Σ^{μν}] = 0

-- We can form odd-dimensional (irriducible) representations by adding Γ (or -Γ), the "fifth gamma matrix"

Γ : {k : Nat} -> 
    Vect (k*2+2) $ Matrix (power 2 $ S k) (power 2 $ S k) (Complex Float) -> 
    Matrix (power 2 $ S k) (power 2 $ S k) (Complex Float) 
Γ {k} gs = mScale (gPhase k) (applyAll gs) where
  gPhase : Nat -> Complex Float 
  gPhase Z     = c0
  gPhase (S n) = cmi * (gPhase n)
  applyAll : Num t => Vect n (Matrix m m t) -> Matrix m m t
  applyAll [m]              = m
  applyAll (m :: (h :: ms)) = applyAll ((m <> h) :: ms)


---------- Proofs ----------

total 
multTwoRightPlusTimesOne : (n : Nat) -> mult n 2 = n + (mult n 1)
multTwoRightPlusTimesOne = proof
  intros
  rewrite (multRightSuccPlus n (S Z))
  trivial

total 
multTwoRightPlus : (n : Nat) -> n * 2 = plus n n
multTwoRightPlus = proof
  intros
  rewrite (sym $ multTwoRightPlusTimesOne n)
  rewrite (sym $ multOneRightNeutral n)
  trivial

total 
plusPlusZero : (x,y : Nat) -> x + y = x + (y + 0)
plusPlusZero = proof
  intros
  rewrite (sym $ plusZeroRightNeutral y)
  trivial

Gamma_Lemma = proof
  intros
  rewrite (plusZeroRightNeutral (plus (mult k 2) 2))
  rewrite (sym $ plusSuccRightSucc (plus (mult k 2) 2) 0)
  rewrite (sym $ plusSuccRightSucc (plus (mult k 2) 2) 1)
  rewrite (sym $ plusZeroRightNeutral (power 2 k))
  rewrite (sym $ plusZeroRightNeutral (power 2 k + (power 2 k)))
  rewrite (multTwoRightPlus (plus (power 2 k) (power 2 k)))
  rewrite (sym $ plusPlusZero (power 2 k) (power 2 k))
  trivial

Γ_Lemma = proof
  intros
  rewrite (plusZeroRightNeutral (plus (mult k 2) 2))
  rewrite (sym $ plusSuccRightSucc (plus (mult k 2) 2) 0)
  rewrite (sym $ plusSuccRightSucc (plus (mult k 2) 2) 1)
  rewrite (sym $ plusZeroRightNeutral (power 2 k))
  rewrite (sym $ plusZeroRightNeutral (power 2 k + (power 2 k)))
  rewrite (multTwoRightPlus (plus (power 2 k) (power 2 k)))
  rewrite (sym $ plusPlusZero (power 2 k) (power 2 k))
  trivial


