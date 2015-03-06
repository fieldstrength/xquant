module Marked

import Data.Fin
import Data.Vect


%default total


||| A set of sites that are either marked (X) or unmarked (O)
||| @ n number of sites
||| @ m number of marked sites
data Marks : (n : Nat) -> (m : Nat) -> Type where
  mZ : Marks Z Z
  mX : Marks n m -> Marks (S n) (S m)
  mO : Marks n m -> Marks (S n) m

||| Proof that a site is marked at the given position
data XAt : Fin n -> Marks n m -> Type where
  isX      : XAt FZ (mX y)
  shiftX_X : XAt f y -> XAt (FS f) (mX y)
  shiftO_X : XAt f y -> XAt (FS f) (mO y)

||| Proof that a site is unmarked at the given position
data OAt : Fin n -> Marks n m -> Type where
  isO      : OAt FZ (mO x)
  shiftX_O : OAt f x -> OAt (FS f) (mX x)
  shiftO_O : OAt f x -> OAt (FS f) (mO x)

oNotX : XAt FZ (mO x) -> Void
oNotX isX impossible

xNotO : OAt FZ (mX x) -> Void
xNotO isO impossible

||| Compatibility between marked sets such that they can be added without clashing
data Compat : Marks n m -> Marks n j -> Type where
  comZero : Compat mZ mZ
  comOO   : Compat y z -> Compat (mO y) (mO z)
  comOX   : Compat y z -> Compat (mO y) (mX z)
  comXO   : Compat y z -> Compat (mX y) (mO z)

||| Add two compatible marked sets together
markAdd : {q : Marks n m} -> {w : Marks n j} -> Compat q w -> Marks n (m + j)
markAdd comZero    = mZ
markAdd (comOO c)  = mO (markAdd c)
markAdd (comOX c) ?= mX (markAdd c)
markAdd (comXO c)  = mX (markAdd c)

||| The dual of a marked set, status of every site switched
dual : Marks n m -> Marks n (n - m)
dual mZ      = mZ
dual (mX q)  = mO $ dual q
dual (mO q) ?= mX $ dual q

shift : LTE n m -> LTE n (S m)
shift LTEZero     = LTEZero
shift (LTESucc l) = LTESucc (shift l) 

markBound : Marks n m -> LTE m n
markBound mZ = LTEZero
markBound (mX q) with (markBound q)
  | w = LTESucc w
markBound (mO q) with (markBound q)
  | LTEZero   = LTEZero
  | LTESucc x = LTESucc $ shift x

minusSuccLeft : (n,m : Nat) -> LTE m n -> (S n) - m = S (n - m)
minusSuccLeft n     Z     LTEZero = ?minusSuccLeft_rhs_1
minusSuccLeft (S n) (S m) (LTESucc l) with (minusSuccLeft n m l)
  | eqn = ?minusSuccLeft_rhs_2

Empty : (n : Nat) -> Marks n Z
Empty Z     = mZ
Empty (S n) = mO $ Empty n

--------------------------------------------------------
--       Conversion to/from Vect for convenience
--------------------------------------------------------

data Mark = O | X

toV : Marks n m -> Vect n Mark
toV mZ     = []
toV (mX q) = X :: (toV q)
toV (mO q) = O :: (toV q)

fromV : Vect n Mark -> (m : Nat ** Marks n m)
fromV []        = (_ ** mZ)
fromV (X :: xs) = (_ ** mX $ getProof $ fromV xs)
fromV (O :: xs) = (_ ** mO $ getProof $ fromV xs)

--------------------------------------------------------
--                    Partitions
--------------------------------------------------------

||| A partition of a set of sites into subsets
data Partition : (x : Marks n m) -> Type where
  POne : (y : Marks n m) -> Partition y
  PNxt : (y : Marks n m) -> (c : Compat y z) -> Partition $ markAdd c

-- Trouble type-checking Partition example: Idris-dev issue # 1805

||| A complete partition of a set of sites into subsets
data PartitionOfUnity : Nat -> Type where
  PUnity : {m : Marks n n} -> (p : Partition m) -> PartitionOfUnity n

||| A partition of a set of sites into subsets of a particular size
||| @ i the size of the subsets
||| @ x which sites are included in the partition
data PartitionBy : (i : Nat) -> (x : Marks n m) -> Type where
  PBZero : {i,n : Nat} -> PartitionBy i (Empty n)
  PBNext : {y : Marks n i} -> (c : Compat y z) -> PartitionBy i z -> PartitionBy i $ markAdd c

||| A complete partition of a set of sites into subsets of a fixed size
||| @ i the size of the subsets
||| @ n the size of the partitioned set
data PartitionOfUnityBy : (i : Nat) -> (n : Nat) -> Type where
  PUnityBy : {x : Marks n n} -> (p : PartitionBy i x) -> PartitionOfUnityBy i n


---------- Proofs ----------

markAdd_lemma_1 = proof
  intros
  rewrite plusSuccRightSucc m j
  trivial


dual_lemma_1 = proof
  intros
  let prf = markBound q
  let msl = minusSuccLeft n m prf
  rewrite sym msl
  trivial


minusSuccLeft_rhs_1 = proof
  intros
  rewrite sym $ minusZeroRight n
  trivial

minusSuccLeft_rhs_2 = proof
  intros
  trivial
