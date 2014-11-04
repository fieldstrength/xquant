
module Hilbert

import Matrix
import Data.Complex


infixl 3 <|>

----------------------------------------------------------------------------------
--                               Hilbert Space Types
----------------------------------------------------------------------------------

||| Type function for state vector in the n-dimensional complex Hilbert space
StateSpace : Nat -> Type -> Type
StateSpace n a = Vect n (Complex a)

||| n-dimensional quantum observable datatype ~ n x n complex matrices 
Op : Nat -> Type -> Type
Op n a = Matrix n n (Complex a)

||| n-dimensional ket vector as a proper n x 1 matrix collumn
KetSpace : Nat -> Type -> Type
KetSpace n a = Matrix n 1 (Complex a)

||| n-dimensional bra vector as a proper 1 x n matrix row
BraSpace : Nat -> Type -> Type
BraSpace n a = Matrix 1 n (Complex a)


-- Shorthand for the n-qubit state space, 2^n dimensional Hilbert space 
Qubit : Nat -> Type -> Type
Qubit n a = StateSpace (power 2 n)a 

-- Shorthand for n-qubit statespace observable type
QubitOp : Nat -> Type -> Type
QubitOp n a = let m = power 2 n in Matrix m m (Complex a)

-- Shorthand for n-qubit collumn vector matrix type
QubitKet : Nat -> Type -> Type
QubitKet n a = let m = power 2 n in Matrix m 1 (Complex a)

-- Shorthand for n-qubit row vector matrix type
QubitBra : Nat -> Type -> Type
QubitBra n a = let m = power 2 n in Matrix 1 m (Complex a)


-------------------------------------------------------------------------------------------
--                          Functions on States and Operators
-------------------------------------------------------------------------------------------

-- Normalize
normalize : StateSpace n Float -> StateSpace n Float
normalize q = let sqn = sum $ map ((\x => x*x) . magnitude) q in 
  map (\(r :+ i) => (r / (sqrt sqn)) :+ (i / (sqrt sqn))) q 

conjugate : Group a => Complex a -> Complex a
conjugate (r :+ i) = r :+ inverse i

-- Infix Hilbert inner product
(<|>) : StateSpace n Float -> StateSpace n Float -> Complex Float
(<|>) q w = sum $ zipWith (*) (map Complex.conjugate q) w

-- Hermitian conjugate (adjoint) on complex matrices
dagger : Group a => Matrix n m (Complex a) -> Matrix m n (Complex a)
dagger h = map (map Hilbert.conjugate) $ transpose h

bra : Group a => StateSpace n a -> BraSpace n a
bra v = dagger $ col v

----------------------------------------------------------------------------------
--                               State Primatives
----------------------------------------------------------------------------------

-- Standard position basis vector
cbasis : {n : Nat} -> (Fin n) -> StateSpace n Float
cbasis {n} f = basis f

-- Nat to Float conversion, needed below
natToFloat : Nat -> Float
natToFloat Z     = 0.0
natToFloat (S k) = 1.0 + (natToFloat k)

-- Momentum basis
--   using helper function: pBasis _ n p x  ~  e^(2 π i p x / n) :: ...
pbasis : (N : Nat) -> Nat -> StateSpace N Float
pbasis n p = pBasis n n p Z where
  pBasis : (l : Nat) -> Nat -> Nat -> Nat -> StateSpace l Float
  pBasis Z     _ _ _ = Nil
  pBasis (S k) n p x = cis (pi * 2 * (natToFloat $ mult p x) / (natToFloat n)) :: pBasis k n p (S x)

-- Standard Kets and Bras
sKet : (Fin d) -> KetSpace d Float
sKet f = col (cbasis f)

sRow : (Fin d) -> BraSpace d Float
sRow f = row (cbasis f)

-- Normalized N-qubit QHZ ket 
GHZ : (N : Nat) -> QubitKet N Float
GHZ k = col $ normalize $ ghz (power 2 k) (power 2 k) where
  ghz : (n : Nat) -> Nat -> StateSpace n Float
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

