module Graphs

import Data.Vect


%default total


--   Graph p v ~ (lines, vertices)
data Graph : Nat -> Nat -> Type where
  gInit : (p : Nat) -> Graph p Z
  vertx : Graph p v -> Vect n (Fin $ 2*p) -> Graph p (S v)

--   ScalarGraph n l v e ~ (lines per vertex, lines, vertices)
data ScalarGraph : Nat -> Nat -> Nat -> Type where
  grfInit : (n : Nat) -> (l : Nat) -> ScalarGraph n l Z
  vertex : Vect n (Fin (2*p)) -> LTE (n*(S v)) (p*2) -> ScalarGraph n p v -> ScalarGraph n p (S v)

-- The number of external lines is the number of half-edges not connected to vertices
external : ScalarGraph n p v -> Nat
external {n} {p} {v} g = 2*p - n*v

-- basic graph type indexed by numer of vertices
data PropGraph : Nat -> Type where
  pInit : PropGraph Z
  prop  : Nat -> Nat -> PropGraph k -> PropGraph (S k)

-----------------------
-- Proofs for Graphs
-----------------------

-- type-specific proof that zero is less than n
zeroLess : (n : Nat) -> LTE 0 n
zeroLess n = LTEZero

displaceBy : (n : Nat) -> LTE 0 m -> LTE n (n + m)
displaceBy Z     pf = pf
displaceBy (S k) pf = LTESucc $ displaceBy k pf

constructLTE : (n,m : Nat) -> LTE n (n + m)
constructLTE n m = displaceBy n $ zeroLess m

-- proof that # of vertices v within appropriate bound
vertexBound : ScalarGraph n p v -> LTE (n*v) (2*p)
vertexBound (vertex vx pf g) ?= {Vertex_Lemma_3} pf
vertexBound (grfInit n p)    ?= {Vertex_Lemma_4} zeroLess (2*p)

---------------------------
-- Scalar Graph Examples
---------------------------

phi3vac : ScalarGraph 3 0 0 
phi3vac = grfInit 3 0

threeprops : ScalarGraph 3 3 0
threeprops = grfInit 3 3

d1 : ScalarGraph 3 3 1
d1 = vertex [0,1,2] (constructLTE 3 3) $ grfInit 3 3

--------------------------------------------
--       Functions on scalar graphs 
--------------------------------------------

-- retrieve the propagator assignments for each vertex, as one array
partial
verts : ScalarGraph n p v -> Vect (n*v) (Fin $ 2*p)
verts (vertex v _ g) ?= {Vertex_Lemma} v ++ (verts g)
--verts (grfInit Z Z)  ?= ?rhs -- {Lem_2} Vect.Nil

-- More...

------------------------------------------
-- Vector intersections, uniqueness, sets
------------------------------------------

intersect : Eq a => Vect n a -> Vect m a -> (l : Nat ** Vect l a)
intersect Nil       _   = (_ ** Nil)
intersect _         Nil = (_ ** Nil)
intersect (v :: vs) ws with (intersect vs ws)
  | (_ ** r) = if elem v ws then (_ ** (v :: r)) else (_ ** r)

uniqueOnly : Eq a => Vect n a -> (l : Nat ** Vect l a)
uniqueOnly Nil = (_ ** Nil)
uniqueOnly (x :: xs) with (uniqueOnly xs)
  | (_ ** v) = if elem x xs then (_ ** v) else (_ ** x :: v)

numUnique : Eq a => Vect n a -> Nat
numUnique v = (\(n ** v) => n) $ uniqueOnly v

data Set : Vect n a -> Type where
  SNil      : Set Nil
  Singleton : (x : a) -> Set [x]
  SApp      : (x : a) -> (Not $ Elem x v) -> Set v -> Set (x :: v)

partial
setMaker : DecEq a => (v : Vect n a) -> (m : Nat ** (z : Vect m a ** Set z))
setMaker Nil = (_ ** (_ ** SNil))
setMaker [x] = (_ ** (_ ** Singleton x))
{-
setMaker (x :: xs) with (isElem x xs)
  | Yes prf = setMaker xs
  | No contra with (setMaker xs)
    | (k ** (v ** s)) = (_ ** (_ ** (SApp x contra s)))
--}

instance Show (Fin n) where
  show {n} f = "F[" ++ (show $ (+1) $ cast {to=Integer} f) ++ "/" ++ (show n) ++ "]"

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

Vertex_Lemma = proof
  intros
  rewrite sym $ multRightSuccPlus n v
  trivial

Vertex_Lemma_3 = proof
  intros
  rewrite sym $ plusZeroRightNeutral p
  rewrite multTwoRightPlus p
  trivial

Vertex_Lemma_4 = proof
  intros
  rewrite sym $ multZeroRightZero n
  rewrite sym $ plusZeroRightNeutral p
  rewrite multTwoRightPlus p
  rewrite multCommutative 2 p
  trivial

