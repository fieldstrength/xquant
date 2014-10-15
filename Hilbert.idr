
module Hilbert

import Matrix
import Data.Complex


infixl 3 <|>
infixr 3 ><

----------------------------------------------------------------------------------
--                               Hilbert Space Types
----------------------------------------------------------------------------------

-- State vector in the n-dimensional complex Hilbert space
StateSpace : Nat -> Type
StateSpace n = Vect n (Complex Float)

-- n-dimensional quantum observable datatype ~ n x n complex matrices 
Obs : Nat -> Type
Obs n = Matrix n n (Complex Float)

-- n-dimensional Ket vector as a proper n x 1 matrix collumn
KetSpace : Nat -> Type
KetSpace n = Matrix n 1 (Complex Float)

-- n-dimensional Bra vector as a proper 1 x n matrix row
BraSpace : Nat -> Type
BraSpace n = Matrix 1 n (Complex Float)


-- Shorthand for the n-qubit state space, 2^n dimensional Hilbert space 
Qubit : Nat -> Type
Qubit n = StateSpace (power 2 n)

-- Shorthand for n-qubit statespace observable type
QubitObs : Nat -> Type
QubitObs n = let m = power 2 n in Matrix m m (Complex Float)

-- Shorthand for n-qubit collumn vector matrix type
QubitKet : Nat -> Type
QubitKet n = let m = power 2 n in Matrix m 1 (Complex Float)

-- Shorthand for n-qubit row vector matrix type
QubitBra : Nat -> Type
QubitBra n = let m = power 2 n in Matrix 1 m (Complex Float)


-------------------------------------------------------------------------------------------
--                          Functions on States and Operators
-------------------------------------------------------------------------------------------

-- Normalize
normalize : StateSpace n -> StateSpace n
normalize q = let sqn = sum $ map ((\x => x*x) . magnitude) q in 
  map (\(r :+ i) => (r / (sqrt sqn)) :+ (i / (sqrt sqn))) q 

-- Hilbert Inner product – conjugates first argument
inner : StateSpace n -> StateSpace n -> Complex Float
inner q w = sum $ zipWith (*) (map conjugate q) w

-- Infix Hilbert inner product
(<|>) : StateSpace n -> StateSpace n -> Complex Float
(<|>) = inner

-- Hermitian conjugate (adjoint) on complex matrices
dagger : Matrix n m (Complex Float) -> Matrix m n (Complex Float)
dagger h = map (map conjugate) $ transpose h

bra : StateSpace n -> BraSpace n
bra v = dagger $ col v

Neutral : (n : Nat) -> StateSpace n
Neutral Z = []
Neutral (S k) = (1 :+ 0) :: (Neutral k) 



----------------------------------------------------------------------------------
--                               State Primatives
----------------------------------------------------------------------------------

-- Standard position basis vector
cbasis : {n : Nat} -> (Fin n) -> StateSpace n
cbasis {n} f = basis {n} f

-- Nat to Float conversion, needed below
natToFloat : Nat -> Float
natToFloat Z     = 0.0
natToFloat (S k) = 1.0 + (natToFloat k)

-- Momentum basis
--   using helper function: pBasis _ n p x  ~  e^(2 π i p x / n) :: ...
pbasis : (N : Nat) -> Nat -> StateSpace N
pbasis n p = pBasis n n p Z where
  pBasis : (l : Nat) -> Nat -> Nat -> Nat -> StateSpace l
  pBasis Z     _ _ _ = Nil
  pBasis (S k) n p x = cis (pi * 2 * (natToFloat $ mult p x) / (natToFloat n)) :: pBasis k n p (S x)

-- Standard Kets and Bras
sKet : {d : Nat} -> (Fin d) -> KetSpace d
sKet f = col (cbasis f)

sRow : {d : Nat} -> (Fin d) -> BraSpace d
sRow f = row (cbasis f)

-- Normalized N-qubit QHZ ket 
GHZ : (N : Nat) -> QubitKet N
GHZ k = col $ normalize $ ghz (power 2 k) (power 2 k) where
  ghz : (n : Nat) -> Nat -> StateSpace n
  ghz (S Z) k     = [(1 :+ 0)]
  ghz (S j) (S k) = let s = if j == k then (1 :+ 0) else (0 :+ 0) in s :: (ghz j (S k))


-------------------------------------------------------------------------------------------
--                                     Miscellany
-------------------------------------------------------------------------------------------

-- Complex number divide 
(/) : Complex Float -> Complex Float -> Complex Float
(/) (a:+b) (c:+d) = let real = (a*c+b*d)/(c*c+d*d) in let imag = (b*c-a*d)/(c*c+d*d) in (real :+ imag)

-- Basic complex units
c1 : Complex Float
c1 = 1 :+ 0

c0 : Complex Float
c0 = 0 :+ 0

ci : Complex Float 
ci = 0 :+ 1

cmi : Complex Float
cmi = 0 :+ -1

cm1 : Complex Float
cm1 = -1 :+ 0
