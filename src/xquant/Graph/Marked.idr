module xquant.Graph.Marked

-- import Pruviloj
import xquant.Math.Set

%default total

||| Marks are used to signify sets of sites that are either
||| occupied (X) or not (O)
data Mark = X | O

||| Increment a Nat if X, do nothing if O.
||| Used to count total number of marks that are X.
mS : Mark -> Nat -> Nat
mS X = S
mS O = id

||| Representation of a set of sites
||| @ n total number of sites
||| @ k numer that are occupied with X
data Marks : (n : Nat) -> (k : Nat) -> Type where
  Nil  : Marks Z Z
  (::) : (m : Mark) -> Marks n k -> Marks (S n) (mS m k)

empty_ : (n : Nat) -> Marks n Z
empty_ Z     = []
empty_ (S k) = O :: empty_ k

empty : {n : Nat} -> Marks n Z
empty = empty_ _

insertMk : Fin n -> (y : Mark) -> Marks n j -> Marks (S n) (mS y j)
insertMk FZ     y m        = y :: m
insertMk (FS i) X (X :: m) = X :: insertMk i X m
insertMk (FS i) O (X :: m) = X :: insertMk i O m
insertMk (FS i) X (O :: m) = O :: insertMk i X m
insertMk (FS i) O (O :: m) = O :: insertMk i O m

--countMZero : (n : Nat) -> Set [empty_ n]


data Compat : Marks n k -> Marks n j -> Type where
  ComZero : Compat [] []
  ComOO   : Compat q w -> Compat (O :: q) (O :: w)
  ComXO   : Compat q w -> Compat (X :: q) (O :: w)
  ComOX   : Compat q w -> Compat (O :: q) (X :: w)

pL : {x : Marks n k} -> {y : Marks n j} -> Compat x y -> Marks n k
pL {x} c = x

pR : {x : Marks n k} -> {y : Marks n j} -> Compat x y -> Marks n j
pR {y} c = y



||| Add two compatible marked sets together
markAdd : {q : Marks n m} -> {w : Marks n j} -> Compat q w -> Marks n (m + j)
markAdd ComZero    = []
markAdd (ComOO c)  = O :: (markAdd c)
markAdd (ComOX c) ?= X :: (markAdd c)
markAdd (ComXO c)  = X :: (markAdd c)

markAdd_lemma_1 = proof
  intros
  rewrite plusSuccRightSucc m j
  trivial

{-
markLem : Elab ()
markLem = do ns <- intros
             rewriteWith `(plusSuccRightSucc ~(Var m1) ~(Var j))
             hypothesis

mlem = %runElab markLem
-}

Marks_ : Nat -> Type
Marks_ n = (m ** Marks n m)


shift : LTE n m -> LTE n (S m)
shift LTEZero     = LTEZero
shift (LTESucc l) = LTESucc (shift l)


markBound : Marks n m -> LTE m n
markBound [] = LTEZero
markBound (X :: q) with (markBound q)
  | w = LTESucc w
markBound (O :: q) with (markBound q)
  | LTEZero   = LTEZero
  | LTESucc x = LTESucc $ shift x


XXnotCompat : Compat (X :: ys) (X :: zs) -> Void
XXnotCompat ComZero impossible

XOunfold : Compat (X :: ys) (O :: zs) -> Compat ys zs
XOunfold (ComXO c) = c

OXunfold : Compat (O :: ys) (X :: zs) -> Compat ys zs
OXunfold (ComOX c) = c

OOunfold : Compat (O :: ys) (O :: zs) -> Compat ys zs
OOunfold (ComOO c) = c


antiCom : Not (Compat xs ys) -> Not $ Compat (q::xs) (w::ys)
antiCom contra ComZero impossible


decer : (m1 : Marks n i) -> (m2 : Marks n j) -> Dec (Compat m1 m2)
decer []        []        = Yes ComZero
decer (X :: ys) (X :: zs) = No  XXnotCompat
decer (X :: ys) (O :: zs) with (decer ys zs)
  decer (X :: ys) (O :: zs) | Yes prf = Yes $ ComXO prf
  decer (X :: ys) (O :: zs) | No contra = No $ antiCom contra
decer (O :: ys) (X :: zs) with (decer ys zs)
  decer (O :: ys) (X :: zs) | Yes prf = Yes $ ComOX prf
  decer (O :: ys) (X :: zs) | No contra = No $ antiCom contra
decer (O :: ys) (O :: zs) with (decer ys zs)
  decer (O :: ys) (O :: zs) | Yes prf = Yes $ ComOO prf
  decer (O :: ys) (O :: zs) | No contra = No $ antiCom contra

partial
add' : (m1 : Marks n i) -> (m2 : Marks n j) -> Compat m1 m2
add' m1 m2 with (decer m1 m2)
  | Yes c = c


data Compatible : List (Marks_ n) -> Marks_ n -> Type where
  OneCom : (m : Marks_ n) -> Compatible [m] m
  NextCom : (m : Marks_ n)
         -> Compatible l m0
         -> {c : Compat (getProof m) (getProof m0)}
         -> Compatible (m::l) (_ ** markAdd c)

data CompatSet : Nat -> Type where
  CompSet : {m : Marks_ n} -> (Compatible l m) -> CompatSet n

mkComp : Marks n j -> CompatSet n
mkComp m = CompSet $ OneCom (_ ** m)

partial comp' : (x : Marks_ n) -> Compatible l m -> (j ** Compatible (x::l) j)
comp' {m} x allc with (decer (getProof x) (getProof m))
  | Yes c = (_ ** NextCom {c} x allc)

partial comp : (x : Marks_ n) -> CompatSet n -> CompatSet n
comp x (CompSet c) = CompSet $ getProof $ comp' x c

||| A partition of a set of sites into subsets
data Partition : (x : Marks n m) -> Type where
  POne  : (y : Marks n m) -> Partition y
  PNext : (y : Marks n m) -> (c : Compat y z) -> Partition z -> Partition (markAdd c)


||| A complete partition of a set of sites into subsets
data PartitionOfUnity : Nat -> Type where
  PUnity : {m : Marks n n} -> (p : Partition m) -> PartitionOfUnity n

||| A partition of a set of sites into subsets of a particular size
||| @ i the size of the subsets
||| @ x which sites are included in the partition
data PartitionBy : (i : Nat) -> (x : Marks n m) -> Type where
  PBZero : PartitionBy i (empty_ n)
  PBNext : {y : Marks n i} -> (c : Compat y z) -> PartitionBy i z -> PartitionBy i (markAdd c)

||| A complete partition of a set of sites into subsets of a fixed size
||| @ i the size of the subsets
||| @ n the size of the partitioned set
data PartitionOfUnityBy : (i : Nat) -> (n : Nat) -> Type where
  PUnityBy : {x : Marks n n} -> (p : PartitionBy i x) -> PartitionOfUnityBy i n


||| The dual of a marked set, status of every site switched
dual : Marks n m -> Marks n (n `minus` m)
dual []      = []
dual (X :: q)  = O :: dual q
dual (O :: q) ?= X :: dual q


test1 : Partition [X,O]
test1 = POne [X,O]

test2 : Partition [X,X]
test2 = PNext [O,X] (ComOX (ComXO ComZero)) test1


---------- Proofs ----------



minusSuccLeft : (n,m : Nat) -> LTE m n -> (S n) `minus` m = S (n `minus` m)
minusSuccLeft n     Z     LTEZero = ?minusSuccLeft_rhs_1
minusSuccLeft (S n) (S m) (LTESucc l) with (minusSuccLeft n m l)
  | eqn = ?minusSuccLeft_rhs_2

minusSuccLeft_rhs_1 = proof
  intros
  rewrite sym $ minusZeroRight n
  trivial

minusSuccLeft_rhs_2 = proof
  intros
  trivial

dual_lemma_1 = proof
  intros
  let prf = markBound q
  let msl = minusSuccLeft n k prf
  rewrite sym msl
  trivial
