
module SigKets

import Data.Complex
import Data.ZZ
import Data.Matrix
import Sigmas
import math.Hilbert


infixl 3 <\>
infixl 3 <|>
infixr 4 </>
infixr 7 <&>


-------------------------------------------------------------------------------------------
--                                     State Data
-------------------------------------------------------------------------------------------

-- Spin orientation datatype - no identity option, unlike Pauli data type,
--   though it could possibly be added to represent a neutral density matrix
data Orient = X | Y | Z

data Spin = Up | Down

instance Eq Spin where 
  Up == Up     = True
  Down == Down = True
  Up == Down   = False
  Down == Up   = False

-- basic spin orientation datatype
data EigenSpin = Eigenspin Orient Spin

-- collumn 'ket' vector for multiple spins
data KetSpins : Nat -> Type where 
  kPhase : Phase -> KetSpins Z
  kS     : EigenSpin -> KetSpins k -> KetSpins (S k)

-- row 'bra' vector for multiple spins
data BraSpins : Nat -> Type where 
  bPhase : Phase -> BraSpins Z
  bS     : EigenSpin -> BraSpins k -> BraSpins (S k)

-- convert a bra to a ket
bk : BraSpins n -> KetSpins n
bk (bPhase p) = kPhase $ star p
bk (bS e bs)  = kS e (bk bs)

-- convert a ket to a bra
kb : KetSpins n -> BraSpins n
kb (kPhase p) = bPhase $ star p
kb (kS e ks)  = bS e (kb ks)

-- easy initialize bra
bra : EigenSpin -> BraSpins 1
bra e = bS e $ bPhase P1

-- easy initialize ket
ket : EigenSpin -> KetSpins 1
ket e = kS e $ kPhase P1

instance Show Orient where
  show X = "X"
  show Y = "Y"
  show Z = "Z"

instance Show Spin where
  show Up   = "Up"
  show Down = "Dn"

instance LaTeX EigenSpin where
  TeX (Eigenspin o Up)   = "\\uparrow_"   ++ (toLower $ show o)
  TeX (Eigenspin o Down) = "\\downarrow_" ++ (toLower $ show o)
  
instance Show EigenSpin where
  show (Eigenspin o s) = (show o) ++ "-" ++ (show s)
  

-- EigenSpin shorthands
upX : EigenSpin
upX = Eigenspin X Up
downX : EigenSpin
downX = Eigenspin X Down

upY : EigenSpin
upY = Eigenspin Y Up
downY : EigenSpin
downY = Eigenspin Y Down

upZ : EigenSpin
upZ = Eigenspin Z Up
downZ : EigenSpin
downZ = Eigenspin Z Down

uX : EigenSpin
uX = upX
dX : EigenSpin
dX = downX

uY : EigenSpin
uY = upY
dY : EigenSpin
dY = downY

uZ : EigenSpin
uZ = upZ
dZ : EigenSpin
dZ = downZ


-- Single abstract sigma acting on ket
ObsKet1 : Sigma 1 -> KetSpins 1 -> KetSpins 1
ObsKet1 (Sig SI $ sPhase p1) (kS (Eigenspin o ud)   (kPhase p2)) = kS (Eigenspin o ud)   (kPhase $ p1 <+> p2)
ObsKet1 (Sig SX $ sPhase p1) (kS (Eigenspin X Up)   (kPhase p2)) = kS (Eigenspin X Up)   (kPhase $ p1 <+> p2)
ObsKet1 (Sig SX $ sPhase p1) (kS (Eigenspin X Down) (kPhase p2)) = kS (Eigenspin X Down) (kPhase $ p1 <+> p2 <+> M1)
ObsKet1 (Sig SX $ sPhase p1) (kS (Eigenspin Y Up)   (kPhase p2)) = kS (Eigenspin Y Down) (kPhase $ p1 <+> p2 <+> Pi)
ObsKet1 (Sig SX $ sPhase p1) (kS (Eigenspin Y Down) (kPhase p2)) = kS (Eigenspin Y Up)   (kPhase $ p1 <+> p2 <+> P1)
ObsKet1 (Sig SX $ sPhase p1) (kS (Eigenspin Z Up)   (kPhase p2)) = kS (Eigenspin Z Down) (kPhase $ p1 <+> p2)
ObsKet1 (Sig SX $ sPhase p1) (kS (Eigenspin Z Down) (kPhase p2)) = kS (Eigenspin Z Up)   (kPhase $ p1 <+> p2)
ObsKet1 (Sig SY $ sPhase p1) (kS (Eigenspin X Up)   (kPhase p2)) = kS (Eigenspin Y Up)   (kPhase $ p1 <+> p2)
ObsKet1 (Sig SY $ sPhase p1) (kS (Eigenspin X Down) (kPhase p2)) = kS (Eigenspin Y Down) (kPhase $ p1 <+> p2 <+> M1)
ObsKet1 (Sig SY $ sPhase p1) (kS (Eigenspin Y Up)   (kPhase p2)) = kS (Eigenspin Z Down) (kPhase $ p1 <+> p2 <+> Pi)
ObsKet1 (Sig SY $ sPhase p1) (kS (Eigenspin Y Down) (kPhase p2)) = kS (Eigenspin X Up)   (kPhase $ p1 <+> p2 <+> Mi)
ObsKet1 (Sig SY $ sPhase p1) (kS (Eigenspin Z Up)   (kPhase p2)) = kS (Eigenspin Z Down) (kPhase $ p1 <+> p2 <+> Pi)
ObsKet1 (Sig SY $ sPhase p1) (kS (Eigenspin Z Down) (kPhase p2)) = kS (Eigenspin Z Up)   (kPhase $ p1 <+> p2 <+> M1)
ObsKet1 (Sig SZ $ sPhase p1) (kS (Eigenspin X Up)   (kPhase p2)) = kS (Eigenspin X Down) (kPhase $ p1 <+> p2 <+> M1)
ObsKet1 (Sig SZ $ sPhase p1) (kS (Eigenspin X Down) (kPhase p2)) = kS (Eigenspin X Up)   (kPhase $ p1 <+> p2 <+> M1)
ObsKet1 (Sig SZ $ sPhase p1) (kS (Eigenspin Y Up)   (kPhase p2)) = kS (Eigenspin Y Down) (kPhase $ p1 <+> p2 <+> M1)
ObsKet1 (Sig SZ $ sPhase p1) (kS (Eigenspin Y Down) (kPhase p2)) = kS (Eigenspin Y Up)   (kPhase $ p1 <+> p2 <+> M1)
ObsKet1 (Sig SZ $ sPhase p1) (kS (Eigenspin Z Up)   (kPhase p2)) = kS (Eigenspin Z Up)   (kPhase $ p1 <+> p2)
ObsKet1 (Sig SZ $ sPhase p1) (kS (Eigenspin Z Down) (kPhase p2)) = kS (Eigenspin Z Down) (kPhase $ p1 <+> p2 <+> M1)


timesPhase : Phase -> KetSpins n -> KetSpins n
timesPhase p1 (kPhase p2) = kPhase (p1 <+> p2)
timesPhase p1 (kS e es)   = kS e (timesPhase p1 es)

topOrientation : KetSpins (S n) -> Orient
topOrientation (kS (Eigenspin o s) more) = o

topKetSpin : KetSpins (S n) -> EigenSpin
topKetSpin (kS e es) = e

lastSpin : KetSpins (S k) -> EigenSpin
lastSpin (kS e (kPhase ph)) = e
lastSpin (kS e (kS e2 es))  = lastSpin (kS e2 es)

kPack : EigenSpin -> KetSpins 1
kPack e = kS e (kPhase P1)

kGetPhase : KetSpins n -> Phase
kGetPhase (kPhase p)             = p
kGetPhase (kS (Eigenspin o s) x) = kGetPhase x


-- Higher Sigma acting on abstract multi-qubit states
ObsKet : Sigma n -> KetSpins n -> KetSpins n
ObsKet (sPhase p1)  (kPhase p2)  = kPhase $ p1 <+> p2
ObsKet (Sig pl s) (kS k ks) with (ObsKet1 (pack pl) (kPack k)) 
  | r = kS (topKetSpin r) (timesPhase (kGetPhase r) (ObsKet s ks))

-- Infix op for Sigma-Ket multiply
(</>) : Sigma n -> KetSpins n -> KetSpins n
(</>) = ObsKet

-- Infix op for Bra-Sigma multiply
(<\>) : BraSpins n -> Sigma n -> BraSpins n
(<\>) b s = kb $ ObsKet s (bk b)

-- Another alias for Bra-Sigma multiply, for maximal harmony with written convention
(<|>) : BraSpins n -> Sigma n -> BraSpins n
(<|>) = (<\>)


-- LaTeX printing, generic show for multiple qubits
instance LaTeX (KetSpins n) where
  TeX (kPhase $ Sign a b) = (if a then "-" else "") ++ (if b then "i" else "1")
  TeX s                   = (Prefix s) ++ (suffix s) where
    suffix : KetSpins n -> String
    suffix (kPhase ph)        = ""
    suffix (kS p (kPhase ph)) = TeX p
    suffix (kS p s)           = (TeX p) ++ " \\otimes " ++ (suffix s)
    Prefix : KetSpins n -> String
    Prefix (kPhase (Sign a b)) = (if a then "-" else "") ++ (if b then "i " else " ")
    Prefix (kS p s)            = Prefix s

instance Show (KetSpins n) where
  show (kPhase phase) = show phase
  show s = (Prefix s) ++ "[" ++ (suffix s) ++ "]" where
    suffix : KetSpins n -> String
    suffix (kPhase ph)        = ""
    suffix (kS p (kPhase ph)) = (show p)
    suffix (kS p s)           = (show p) ++ (suffix s)
    Prefix : KetSpins n -> String
    Prefix (kPhase (Sign a b)) = (if a then "-" else "") ++ (if b then "i " else "")
    Prefix (kS p s)            = Prefix s



-- tensor product for abstract multi-qubit kets
ox : KetSpins n -> KetSpins m -> KetSpins (n + m)
ox e           (kPhase ph) ?= {Ket_OTimes_Lemma_1} timesPhase ph e
ox (kPhase ph) e            = timesPhase ph e
ox (kS e1 es1) (kS e2 es2) ?= {Ket_OTimes_Lemma_2} ox (dropLast $ kS e1 es1) 
                                                      (kS (lastSpin $ kS e1 es1) (kS e2 es2)) where
  dropLast : KetSpins (S k) -> KetSpins k
  dropLast (kS e (kPhase ph)) = kPhase ph
  dropLast (kS e (kS e2 es))  = kS e (dropLast $ kS e2 es)

-- Infix tensor multiply kets
Ket.(<&>) : KetSpins n -> KetSpins m -> KetSpins (n + m)
Ket.(<&>) = ox

-- Infix tensor multiply bras
Bra.(<&>) : BraSpins n -> BraSpins m -> BraSpins (n + m)
Bra.(<&>) b1 b2 = kb $ ox (bk b1) (bk b2)


-------------------------------------------------------------------------------------------
--                              Numeric State & Operator Data
-------------------------------------------------------------------------------------------

-- Phase to complex number
Phase.comZ : Phase -> Complex ZZ
Phase.comZ (Sign False False) = C1
Phase.comZ (Sign False True)  = Ci
Phase.comZ (Sign True False)  = Cm1
Phase.comZ (Sign True True)   = Cmi

-- Phase to complex float
Phase.comF : Phase -> Complex Float
Phase.comF (Sign False False) = c1
Phase.comF (Sign False True)  = ci
Phase.comF (Sign True False)  = cm1
Phase.comF (Sign True True)   = cmi

-- integral Sigma 1's
sx : QubitOp 1 ZZ
sx = [[C0, C1], [C1, C0]]

sy : QubitOp 1 ZZ
sy = [[C0, Cmi], [Ci, C0]]

sz : QubitOp 1 ZZ
sz = [[C1, C0], [C0, Cm1]]

si : QubitOp 1 ZZ
si = [[C1, C0], [C0, C1]]

Pauli.comZ : Pauli -> QubitOp 1 ZZ
Pauli.comZ SX = sx
Pauli.comZ SY = sy
Pauli.comZ SZ = sz
Pauli.comZ SI = si

-- floating Sigma 1's
Pauli.comF : Pauli -> QubitOp 1 Float
Pauli.comF SX = (0.5 :+ 0) <#> [[c0, c1], [c1, c0]]
Pauli.comF SY = (0.5 :+ 0) <#> [[c0, cmi], [ci, c0]]
Pauli.comF SZ = (0.5 :+ 0) <#> [[c1, c0], [c0, cm1]]
Pauli.comF SI = (0.5 :+ 0) <#> [[c1, c0], [c0, c1]]

-- Sigma n to matrix
Sigma.comF : Sigma n -> QubitOp n Float
Sigma.comF (sPhase ph) = [[comF ph]]
Sigma.comF (Sig p s)   = (comF p) <&> (comF s)

-- Sigma n to matrix
Sigma.comZ : Sigma n -> QubitOp n ZZ
Sigma.comZ (sPhase ph) = [[comZ ph]]
Sigma.comZ (Sig p s)   = (comZ p) <&> (comZ s)


-- Numeric KetSpin vectors
xUp : Qubit 1 Float
xUp = normalize [c1, c1]

xDown : Qubit 1 Float
xDown = normalize [cm1, c1]

yUp : Qubit 1 Float
yUp = normalize [cmi, c1]

yDown : Qubit 1 Float
yDown = normalize [ci, c1]

zUp : Qubit 1 Float
zUp = [c1, c0]

zDown : Qubit 1 Float
zDown = [c0, c1]

-- [single] KetSpin to numeric vector 
Spin.matF : EigenSpin -> QubitKet 1 Float
Spin.matF (Eigenspin X Up)   = col xUp
Spin.matF (Eigenspin X Down) = col xDown
Spin.matF (Eigenspin Y Up)   = col yUp
Spin.matF (Eigenspin Y Down) = col yDown
Spin.matF (Eigenspin Z Up)   = col zUp
Spin.matF (Eigenspin Z Down) = col zDown

-- [single] KetSpin to numeric vector 
KetSpins.matF : KetSpins n -> QubitKet n Float
KetSpins.matF (kPhase ph) = [[comF ph]]
KetSpins.matF (kS e k)    = (Spin.matF e) <&> (KetSpins.matF k)

-- Bra to row-vector matrix
BraSpins.matF : BraSpins n -> QubitBra n Float
BraSpins.matF (bPhase ph) = [[comF (star ph)]]
BraSpins.matF (bS e b)    = (transpose $ Spin.matF e) <&> (BraSpins.matF b)

-- Bra times Ket to complex number
Bra.(<\>) : Ring a => BraSpins n -> KetSpins n -> Complex Float
Bra.(<\>) b k = index 0 $ index 0 $ (matF b) <> (matF k)


||| Sigma operators commute
data Commutes : Sigma n -> Sigma n -> Type where
  CommZero : (x : Sigma Z) -> (y : Sigma Z) -> Commutes x y
  CommSucc : (a : Sigma 1) -> (b : Sigma 1) -> Commutes x y -> Commutes (a <&> x) (b <&> y)

||| Test for Sigma commutation
commute : Sigma n -> Sigma n -> Bool
commute (sPhase x)  (sPhase y)  = True
commute (Sig p1 s1) (Sig p2 s2) = xor (p1 /= p2) $ commute s1 s2

||| All Sigmas of a given order
allSigmas : (n : Nat) -> List $ Sigma n
allSigmas Z     = [sPhase P1]
allSigmas (S n) = allSigmas n >>= (\s => [Sig SI s, Sig SX s, Sig SY s, Sig SZ s])


||| Whether each non-identity Pauli operator occurs an even number of times
qubitParity : List Pauli -> Vect 3 Bool
qubitParity []         = [False, False, False]
qubitParity (SI :: ss) = qubitParity ss
qubitParity (SX :: ss) = updateAt 0 not $ qubitParity ss
qubitParity (SY :: ss) = updateAt 1 not $ qubitParity ss
qubitParity (SZ :: ss) = updateAt 2 not $ qubitParity ss

sigPair : (n : Nat) -> List $ Vect 2 (Sigma n)
sigPair n = [ [s1,s2] | s1 <- (allSigmas n), s2 <- (allSigmas n) ]



---------- Proofs ----------

Ket_OTimes_Lemma_1 = proof
  intro
  rewrite (plusZeroRightNeutral n)
  intros
  trivial

Ket_OTimes_Lemma_2 = proof
  intros
  rewrite sym $ plusSuccRightSucc k (S k1)
  trivial
