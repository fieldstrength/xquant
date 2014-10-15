
module Spinor

import Matrix
import Hilbert

%default total


-- Begin with two primative Gamma matrices, Γ0 and Γ1, generating Spin(2)
-- Define them as both Floating point and symbolic matrices

-- Γ0 = iσy
Gamma0 : QubitObs 1
Gamma0 = [[c0, c1], [cm1, c0]]

-- Γ1 = σx
Gamma1 : QubitObs 1
Gamma1 = [[c0, c1], [c1, c0]]

-- Now construct gammas of for even-dimensional spinor representations (D = 2k + 2) by tensoring as follows:

--    Gamma^μ    = gamma^mu <&> diag(-1,1)  or equivalently:
--    Gamma^μ    = gamma^mu <&> (Gamma1 <> Gamma0)  (where mu <- [0..D-2] )
--
--    Gamma^{D-1} = Id <&> Γ1    = Id ⊗ σx  
--
--    Gamma^D     = Id <&> -iΓ0  = Id ⊗ σy


-- Gamma matrices for even dimensions D = 2k + 2, with size 2^(k+1)
gammaSetEven : (k : Nat) -> Vect (k*2+2) $ Matrix (power 2 (S k)) (power 2 (S k)) (Complex Float)
gammaSetEven Z      = [Gamma0, Gamma1]
gammaSetEven (S k) ?= {Gamma_Lemma} map (\g => g <&> (Gamma1 <> Gamma0)) (gammaSetEven k) 
  ++ [Id <&> Gamma1, Id <&> Gamma0 * cmi]

-- All matrices defined in this way satisy the gamma matrix algebra:

--   {Γμ,Γν} = 2 η{μν} Id   (upstairs indices)

-- They also furnish Poincaré generators faithfully satisfying: i[Σμν,Σσρ] = ηνσΣμρ + ημρΣνσ − ηνρΣμσ − ημσΣνρ 
--   where Σ^{μν} = −i[Γ^μ,Γ^ν]
-- This holds in any dimensionality and in both Minkowski and Euclidean signatures.



-- Now define the "fifth Gamma matrix", denoted Γ

--   Γ = i^{-k} (Γ^0 ... Γ^{D-1})

-- Can form odd-dimensional (irriducible) spinor representations by adding Γ (or -Γ)
Γ : {k : Nat} -> 
    Vect (k*2+2) $ Matrix (power 2 $ S k) (power 2 $ S k) (Complex Float) -> 
    Matrix (power 2 $ S k) (power 2 $ S k) (Complex Float) 
Γ {k} gs = (gPhase k) * (applyAll gs) where
  gPhase : Nat -> Complex Float 
  gPhase Z     = c0
  gPhase (S n) = cmi * (gPhase n)
  applyAll : Num t => Vect n (Matrix m m t) -> Matrix m m t
  applyAll [m]              = m
  applyAll (m :: (h :: ms)) = applyAll ((m <> h) :: ms)
  applyAll Nil              = Id  -- only have this case to satisfy totality check

-- Γ has eigenvalues of ±1 and satisfies:

--   Γ^2 = 1
--   {Γ,Γ^μ} = 0
--   [Γ,Σ^{μν}] = 0


-- AnticommRelation ...


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

