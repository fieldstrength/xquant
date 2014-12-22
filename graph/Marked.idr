module Marked

%default total

data Mark = O | X

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

||| Add two marked lists together 
markAdd : (q : Marks n m) -> (w : Marks n j) -> Compat q w -> Marks n (m + j)
markAdd _      _      comZero    = mZ
markAdd (mO y) (mO z) (comOO c)  = mO (markAdd y z c)
markAdd (mO y) (mX z) (comOX c) ?= mX (markAdd y z c)
markAdd (mX y) (mO z) (comXO c)  = mX (markAdd y z c)


toV : Marks n m -> Vect n Mark
toV mZ     = []
toV (mX q) = X :: (toV q)
toV (mO q) = O :: (toV q)

fromV : Vect n Mark -> (m : Nat ** Marks n m)
fromV []        = (_ ** mZ)
fromV (X :: xs) = (_ ** mX $ getProof $ fromV xs)
fromV (O :: xs) = (_ ** mO $ getProof $ fromV xs)


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


---------- Proofs ----------

dual_lemma_1 = proof
  intros
  let prf = markBound q
  let msl = minusSuccLeft n m prf
  rewrite sym msl
  trivial


minusSuccLeft_rhs_2 = proof
  intros
  trivial


minusSuccLeft_rhs_1 = proof
  intros
  rewrite sym $ minusZeroRight n
  trivial


markAdd_lemma_1 = proof
  intros
  rewrite plusSuccRightSucc m m1
  trivial


