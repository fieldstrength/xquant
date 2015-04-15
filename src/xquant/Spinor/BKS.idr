module xquant.Spinor.BKS

import Data.Vect
import xquant.Spinor.Sigmas
import xquant.Spinor.SigKets

%default total

-----------------------------------------------------------------------
--                           Commutation
-----------------------------------------------------------------------

||| Individual Pauli operators commute iff they are identical up to a phase,
||| or if one of them is the identity
data PauliComm : Pauli -> Pauli -> Type where
  PSame    : (p : Pauli) -> PauliComm p  p
  PIdRight : (p : Pauli) -> PauliComm p  SI
  PIdLeft  : (p : Pauli) -> PauliComm SI p

||| Pauli operators do not commute iff they are not identical up to a phase,
||| and one of them isn't the identity
data PauliNonComm : Pauli -> Pauli -> Type where
  NonCommXY : PauliNonComm SX SY
  NonCommYZ : PauliNonComm SY SZ
  NonCommZX : PauliNonComm SZ SX
  NonCommSwap : PauliNonComm q w -> PauliNonComm w q

||| Decide whether two Pauli operators commute or not
decCommPauli : (x : Pauli) -> (y : Pauli) -> Either (PauliComm x y) (PauliNonComm x y)
decCommPauli SI p  = Left $ PIdLeft p
decCommPauli p  SI = Left $ PIdRight p
decCommPauli SX SX = Left $ PSame SX
decCommPauli SY SY = Left $ PSame SY
decCommPauli SZ SZ = Left $ PSame SZ
decCommPauli SX SY = Right $ NonCommXY
decCommPauli SY SX = Right $ NonCommSwap NonCommXY
decCommPauli SY SZ = Right $ NonCommYZ
decCommPauli SZ SY = Right $ NonCommSwap NonCommYZ
decCommPauli SZ SX = Right $ NonCommZX
decCommPauli SX SZ = Right $ NonCommSwap NonCommZX

mutual
  ||| A pair of commuting Sigma operators is formed by prepending a pair of commuting Paulis
  ||| onto a pair of commuting Sigmas, or by prepending a pair of non-commuting Paulis onto
  ||| a pair of non-commuting Sigmas. Sigmas of level zero (pure numbers) trivially commute.
  data Commuting : Sigma n -> Sigma n -> Type where
    CommPhase : {s1,s2 : Sigma Z} -> Commuting s1 s2
    CommSame  : PauliComm    j k -> Commuting    g h -> Commuting (Sig j g) (Sig k h)
    CommDiff  : PauliNonComm j k -> NonCommuting g h -> Commuting (Sig j g) (Sig k h)

  ||| A pair of non-commuting Sigma operators is formed by prepending a pair of commuting Paulis
  ||| onto a pair of non-commuting Sigmas, or by prepending a pair of non-commuting Paulis onto
  ||| a pair of commuting Sigmas.
  data NonCommuting : Sigma n -> Sigma n -> Type where
    NoCommSame : PauliNonComm j k -> Commuting    g h -> NonCommuting (Sig j g) (Sig k h)
    NoCommDiff : PauliComm    j k -> NonCommuting g h -> NonCommuting (Sig j g) (Sig k h)

||| Decide whether two Sigma operators commute or not
decComm : (x : Sigma n) -> (y : Sigma n) -> Either (Commuting x y) (NonCommuting x y)
decComm (sPhase p1) (sPhase p2) = Left CommPhase
decComm (Sig p1 s1) (Sig p2 s2) with (decComm s1 s2)
  decComm (Sig p1 s1) (Sig p2 s2) | commPrf with (decCommPauli p1 p2)
    decComm (Sig p1 s1) (Sig p2 s2) | Left cm  | Left  cmp = Left  $ CommSame cmp cm
    decComm (Sig p1 s1) (Sig p2 s2) | Left cm  | Right ncp = Right $ NoCommSame ncp cm
    decComm (Sig p1 s1) (Sig p2 s2) | Right nc | Left  cmp = Right $ NoCommDiff cmp nc
    decComm (Sig p1 s1) (Sig p2 s2) | Right nc | Right ncp = Left  $ CommDiff ncp nc

commTest : Vect n (Sigma m) -> Bool
commTest []        = True
commTest (x :: xs) = all (commute x) xs && (commTest xs)

data MutuallyCommuting : Vect n (Sigma m) -> Type where
  IsMutuallyCommuting : (v : Vect n $ Sigma m) ->
                        commTest v = True ->
                        MutuallyCommuting v

data CommStatus : (x : Sigma n) -> (y : Sigma n) -> Type where
  Status_Comm   : Commuting    x y -> CommStatus x y
  Status_NoComm : NonCommuting x y -> CommStatus x y


-----------------------------------------------------------------------
--        Even Parity (for each subspace & generator) datatype
-----------------------------------------------------------------------

data Parity = Even | Odd

data PauliParity = PParity Parity Parity Parity

swap : Parity -> Parity
swap Even = Odd
swap Odd  = Even

updateP : Pauli -> PauliParity -> PauliParity
updateP SX (PParity x y z) = PParity (swap x) y z
updateP SY (PParity x y z) = PParity x (swap y) z
updateP SZ (PParity x y z) = PParity x y (swap z)
updateP SI p               = p

updateParity : Sigma n -> Vect n PauliParity -> Vect n PauliParity
updateParity (sPhase ph) []      = []
updateParity (Sig pl s)  (p::ps) = (updateP pl p) :: (updateParity s ps)

||| Sets of Sigma n operators can be classified by whether each Sigma occurs
||| an even or odd number of times in each single-qubit Hilbert Space
data SigmaParity : Vect n (Sigma m) -> Vect m PauliParity -> Type where
  ParityZero : {m : Nat} -> SigmaParity [] (replicate m $ PParity Even Even Even)
  ParityNext : {v : Vect n (Sigma m)} ->
               (s : Sigma m) ->
               SigmaParity v p ->
               SigmaParity (s::v) (updateParity s p)

data EvenParity : Vect n (Sigma m) -> Type where
  IsEven : {v : Vect n (Sigma m)} ->
           SigmaParity v (replicate m $ PParity Even Even Even) ->
           EvenParity v

evenParity : (n : Nat) -> Vect n PauliParity
evenParity n = replicate n $ PParity Even Even Even


-----------------------------------------------------------------------
--               Multiply-to-Negative-Identity datatype
-----------------------------------------------------------------------

data NegId : Vect n (Sigma m) -> Type where
  IsNegId : (v : Vect (S n) (Sigma m)) ->
            foldr1 (<>) v = negId m ->
            NegId v


-----------------------------------------------------------------------
--                      BKS Theorem datatype
-----------------------------------------------------------------------

data BKS : Vect n (Sigma m) -> Type where
  MkBKS : MutuallyCommuting v ->
          NegId v ->
          EvenParity v ->
          BKS v


-----------------------------------------------------------------------
--      5-qubit BKS proof of David DiVincenzo & Asher Peres
-----------------------------------------------------------------------

zzzzz : Sigma 5
zzzzz = sZ <&> sZ <&> sZ <&> sZ <&> sZ

zxIIx : Sigma 5
zxIIx = sZ <&> sX <&> sI <&> sI <&> sX

xzxII : Sigma 5
xzxII = sX <&> sZ <&> sX <&> sI <&> sI

IxzxI : Sigma 5
IxzxI = sI <&> sX <&> sZ <&> sX <&> sI

IIxzx : Sigma 5
IIxzx = sI <&> sI <&> sX <&> sZ <&> sX

xIIxz : Sigma 5
xIIxz = sX <&> sI <&> sI <&> sX <&> sZ


Asher_David : Vect 6 (Sigma 5)
Asher_David = [zzzzz,
               zxIIx,
               xzxII,
               IxzxI,
               IIxzx,
               xIIxz]


Asher_David_Commuting : MutuallyCommuting Asher_David
Asher_David_Commuting = IsMutuallyCommuting Asher_David Refl

Asher_David_NegId : NegId Asher_David
Asher_David_NegId = IsNegId Asher_David Refl

Asher_David_Parity : SigmaParity Asher_David $ evenParity 5
Asher_David_Parity = ParityNext zzzzz $
                     ParityNext zxIIx $
                     ParityNext xzxII $
                     ParityNext IxzxI $
                     ParityNext IIxzx $
                     ParityNext xIIxz ParityZero

Asher_David_EvenParity : EvenParity Asher_David
Asher_David_EvenParity = IsEven Asher_David_Parity

Asher_David_BKS : BKS Asher_David
Asher_David_BKS = MkBKS Asher_David_Commuting Asher_David_NegId Asher_David_EvenParity


-----------------------------------------------------------------------
--       4-qubit BKS proof of Aravind-Chryssanthacopoulos-Harvey
-----------------------------------------------------------------------

xxxx : Sigma 4
xxxx = sX <&> sX <&> sX <&> sX

xxzz : Sigma 4
xxzz = sX <&> sX <&> sZ <&> sZ

zxxz : Sigma 4
zxxz = sZ <&> sX <&> sX <&> sZ

zxzx : Sigma 4
zxzx = sZ <&> sX <&> sZ <&> sX


Aravind : Vect 4 (Sigma 4)
Aravind = [xxxx,
           xxzz,
           zxxz,
           zxzx]

Aravind_Commuting : MutuallyCommuting Aravind
Aravind_Commuting = IsMutuallyCommuting Aravind Refl

Aravind_NegId : NegId Aravind
Aravind_NegId = IsNegId Aravind Refl

Aravind_Parity : SigmaParity Aravind $ evenParity 4
Aravind_Parity = ParityNext xxxx $
                 ParityNext xxzz $
                 ParityNext zxxz $
                 ParityNext zxzx ParityZero

Aravind_Even_Parity : EvenParity Aravind
Aravind_Even_Parity = IsEven Aravind_Parity

Aravind_BKS : BKS Aravind
Aravind_BKS = MkBKS Aravind_Commuting Aravind_NegId Aravind_Even_Parity
