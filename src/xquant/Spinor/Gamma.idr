module xquant.Spinor.Gamma

import xquant.Core.Types
import public Data.Matrix.Algebraic
import public Control.Algebra.NumericInstances
import public Data.Complex

%default total

-- Begin with two primative Gamma matrices, Γ0 and Γ1, generating Spin(2)

|||  Γ0 = iσy
g0 : Matrix 2 2 (Complex Integer)
g0 = [[c0, c1], [m1, c0]]

|||  Γ1 = σx
g1 : Matrix 2 2 (Complex Integer)
g1 = [[c0, c1], [c1, c0]]

{- Construct gammas for even-dimensional spinor representations (D = 2k + 2)
   First tensor as follows:

      G^μ    = Γ^mu <&> diag(-1,1),  (where mu <- [0..D-2])  or equivalently,
      G^μ    = Γ^mu <&> (g1 <> g0)

   Then adding two new gammas:

      G^{D-1} = Id <&> Γ1    = Id ⊗ σx
      G^D     = Id <&> -iΓ0  = Id ⊗ σy  -}

|||  Gamma matrices for even dimensions D = 2k + 2, with size 2^(k+1)
gammaEven : (k : Nat) -> Vect (k*2 + 2) $ Matrix (power 2 (S k)) (power 2 (S k)) (Complex Integer)
gammaEven Z      = [g0, g1]
gammaEven (S k) ?= {Lemma_1} map (\g => g <&> (g1 <> g0)) (gammaEven k) ++ [Id <&> g1, mi <#> Id <&> g0]

{- Matrices defined in this way satisy the gamma matrix algebra:

     {Γμ,Γν} = 2 η{μν} Id   (upstairs indices)

   They also furnish Poincaré generators   Σ^{μν} = −i[Γ^μ,Γ^ν]
   satisfying, by definition:   i[Σμν,Σσρ] = ηνσΣμρ + ημρΣνσ − ηνρΣμσ − ημσΣνρ

   This holds in any dimensionality and in both Minkowski and Euclidean signatures.

   Now define the "fifth Gamma Matrix", denoted Γ  -}

||| The "fifth gamma matrix" given by
|||
||| Γ = i^{–k} (Γ^0 ... Γ^{D-1})
|||
||| forms an odd-dimensional (irriducible) spinor representation by adding to the appropriate (gammaEven k)
gamma : Vect (k*2+2) $ Matrix (power 2 $ S k) (power 2 $ S k) (Complex Integer) ->
        Matrix (power 2 $ S k) (power 2 $ S k) (Complex Integer)
gamma {k} gs = (pow' mi k) <#> (product' gs)

{- Γ has eigenvalues of ±1 and satisfies:

     Γ^2 = 1
     {Γ,Γ^μ} = 0
     [Γ,Σ^{μν}] = 0  -}

g3 : Matrix 2 2 (Complex Integer)
g3 = product' $ with List [g0,g1]

{-
||| Anticommutation relation, {Γμ,Γν} = 2 η{μν} Id, for D = 2
D2_anticommRelation_00 : (g0 >><< g0) = ((-2 :+ 0) <#> Id)
D2_anticommRelation_00 = Refl

||| Anticommutation relation, {Γμ,Γν} = 2 η{μν} Id, for D = 2
D2_anticommRelation_01 : g0 >><< g1 = [neutral, neutral]
D2_anticommRelation_01 = Refl

||| Anticommutation relation, {Γμ,Γν} = 2 η{μν} Id, for D = 2
D2_anticommRelation_10 : g1 >><< g0 = [neutral, neutral]
D2_anticommRelation_10 = Refl

||| Anticommutation relation, {Γμ,Γν} = 2 η{μν} Id, for D = 2
D2_anticommRelation_11 : g1 >><< g1 = (2 :+ 0) <#> Id
D2_anticommRelation_11 = Refl
-}

---------- Proofs ----------

multTwoRightPlusTimesOne : (n : Nat) -> mult n 2 = n + (mult n 1)
multTwoRightPlusTimesOne = proof
  intros
  rewrite (multRightSuccPlus n (S Z))
  trivial

multTwoRightPlus : (n : Nat) -> n * 2 = plus n n
multTwoRightPlus = proof
  intros
  rewrite (sym $ multTwoRightPlusTimesOne n)
  rewrite (sym $ multOneRightNeutral n)
  trivial

plusPlusZero : (x,y : Nat) -> x + y = x + (y + 0)
plusPlusZero = proof
  intros
  rewrite (sym $ plusZeroRightNeutral y)
  trivial

Lemma_1 = proof
  intros
  rewrite (plusZeroRightNeutral (plus (mult k 2) 2))
  rewrite (sym $ plusSuccRightSucc (plus (mult k 2) 2) 0)
  rewrite (sym $ plusSuccRightSucc (plus (mult k 2) 2) 1)
  rewrite (sym $ plusZeroRightNeutral (power 2 k))
  rewrite (sym $ plusZeroRightNeutral (power 2 k + (power 2 k)))
  rewrite (multTwoRightPlus (plus (power 2 k) (power 2 k)))
  rewrite (sym $ plusPlusZero (power 2 k) (power 2 k))
  trivial
