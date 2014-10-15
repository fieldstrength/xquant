
module SigKets

import Sigmas
import Hilbert


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
ObsKet1 (Sig SI $ sPhase p1) (kS (Eigenspin o ud)   (kPhase p2)) = kS (Eigenspin o ud)   (kPhase $ p1 *~ p2)
ObsKet1 (Sig SX $ sPhase p1) (kS (Eigenspin X Up)   (kPhase p2)) = kS (Eigenspin X Up)   (kPhase $ p1 *~ p2)
ObsKet1 (Sig SX $ sPhase p1) (kS (Eigenspin X Down) (kPhase p2)) = kS (Eigenspin X Down) (kPhase $ p1 *~ p2 *~ M1)
ObsKet1 (Sig SX $ sPhase p1) (kS (Eigenspin Y Up)   (kPhase p2)) = kS (Eigenspin Y Down) (kPhase $ p1 *~ p2 *~ Pi)
ObsKet1 (Sig SX $ sPhase p1) (kS (Eigenspin Y Down) (kPhase p2)) = kS (Eigenspin Y Up)   (kPhase $ p1 *~ p2 *~ P1)
ObsKet1 (Sig SX $ sPhase p1) (kS (Eigenspin Z Up)   (kPhase p2)) = kS (Eigenspin Z Down) (kPhase $ p1 *~ p2)
ObsKet1 (Sig SX $ sPhase p1) (kS (Eigenspin Z Down) (kPhase p2)) = kS (Eigenspin Z Up)   (kPhase $ p1 *~ p2)
ObsKet1 (Sig SY $ sPhase p1) (kS (Eigenspin X Up)   (kPhase p2)) = kS (Eigenspin Y Up)   (kPhase $ p1 *~ p2)
ObsKet1 (Sig SY $ sPhase p1) (kS (Eigenspin X Down) (kPhase p2)) = kS (Eigenspin Y Down) (kPhase $ p1 *~ p2 *~ M1)
ObsKet1 (Sig SY $ sPhase p1) (kS (Eigenspin Y Up)   (kPhase p2)) = kS (Eigenspin Z Down) (kPhase $ p1 *~ p2 *~ Pi)
ObsKet1 (Sig SY $ sPhase p1) (kS (Eigenspin Y Down) (kPhase p2)) = kS (Eigenspin X Up)   (kPhase $ p1 *~ p2 *~ Mi)
ObsKet1 (Sig SY $ sPhase p1) (kS (Eigenspin Z Up)   (kPhase p2)) = kS (Eigenspin Z Down) (kPhase $ p1 *~ p2 *~ Pi)
ObsKet1 (Sig SY $ sPhase p1) (kS (Eigenspin Z Down) (kPhase p2)) = kS (Eigenspin Z Up)   (kPhase $ p1 *~ p2 *~ M1)
ObsKet1 (Sig SZ $ sPhase p1) (kS (Eigenspin X Up)   (kPhase p2)) = kS (Eigenspin X Down) (kPhase $ p1 *~ p2 *~ M1)
ObsKet1 (Sig SZ $ sPhase p1) (kS (Eigenspin X Down) (kPhase p2)) = kS (Eigenspin X Up)   (kPhase $ p1 *~ p2 *~ M1)
ObsKet1 (Sig SZ $ sPhase p1) (kS (Eigenspin Y Up)   (kPhase p2)) = kS (Eigenspin Y Down) (kPhase $ p1 *~ p2 *~ M1)
ObsKet1 (Sig SZ $ sPhase p1) (kS (Eigenspin Y Down) (kPhase p2)) = kS (Eigenspin Y Up)   (kPhase $ p1 *~ p2 *~ M1)
ObsKet1 (Sig SZ $ sPhase p1) (kS (Eigenspin Z Up)   (kPhase p2)) = kS (Eigenspin Z Up)   (kPhase $ p1 *~ p2)
ObsKet1 (Sig SZ $ sPhase p1) (kS (Eigenspin Z Down) (kPhase p2)) = kS (Eigenspin Z Down) (kPhase $ p1 *~ p2 *~ M1)


timesPhase : Phase -> KetSpins n -> KetSpins n
timesPhase p1 (kPhase p2) = kPhase (p1 *~ p2)
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
ObsKet (sPhase p1)  (kPhase p2)  = kPhase $ p1 *~ p2
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
Phase.com : Phase -> Complex Float
Phase.com (Sign False False) = c1
Phase.com (Sign False True)  = ci
Phase.com (Sign True False)  = cm1
Phase.com (Sign True True)   = cmi

-- Numeric Sigma 1's
sx : QubitObs 1
sx = mScale (0.5 :+ 0) [[c0, c1], [c1, c0]]

sy : QubitObs 1 
sy = mScale (0.5 :+ 0) [[c0, cmi], [ci, c0]]

sz : QubitObs 1
sz = mScale (0.5 :+ 0) [[c1, c0], [c0, cm1]]

si : QubitObs 1
si = mScale (0.5 :+ 0) [[c1, c0], [c0, c1]]

-- Pauli to Matrix
Pauli.mat : Pauli -> QubitObs 1
Pauli.mat SX = sx
Pauli.mat SY = sy
Pauli.mat SZ = sz
Pauli.mat SI = si

-- Sigma n to matrix
Sigma.mat : Sigma n -> QubitObs n
Sigma.mat (sPhase ph) = [[com ph]]
Sigma.mat (Sig p s)   = (mat p) <&> (mat s)

-- Numeric KetSpin vectors
xUp : Qubit 1
xUp = normalize [c1, c1]

xDown : Qubit 1
xDown = normalize [cm1, c1]

yUp : Qubit 1
yUp = normalize [cmi, c1]

yDown : Qubit 1
yDown = normalize [ci, c1]

zUp : Qubit 1
zUp = [c1, c0]

zDown : Qubit 1
zDown = [c0, c1]

-- [single] KetSpin to numeric vector 
Spin.mat : EigenSpin -> QubitKet 1
Spin.mat (Eigenspin X Up)   = col xUp
Spin.mat (Eigenspin X Down) = col xDown
Spin.mat (Eigenspin Y Up)   = col yUp
Spin.mat (Eigenspin Y Down) = col yDown
Spin.mat (Eigenspin Z Up)   = col zUp
Spin.mat (Eigenspin Z Down) = col zDown

-- KetSpin n to numeric vector
Ket.mat : KetSpins n -> QubitKet n
Ket.mat (kPhase ph) = [[ com ph ]]
Ket.mat (kS e es)   = (mat e) <&> (mat es)

-- Bra to row-vector matrix
Bra.mat : BraSpins n -> QubitBra n
Bra.mat b = transpose (Ket.mat $ bk b)

-- Bra times Ket to complex number
Bra.(<\>) : BraSpins n -> KetSpins n -> Complex Float
Bra.(<\>) b k = index 0 $ index 0 $ (mat b) <> (mat k) 

          
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
