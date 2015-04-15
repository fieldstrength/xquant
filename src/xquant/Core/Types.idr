module xquant.Core.Types

import public Data.Complex
import public Data.Matrix

%default total


Fl : Type
Fl = Float

Amp : Type
Amp = Complex Fl


---- Hilbert Space types ----

||| State vector type for n-dimensional complex Hilbert space
StateSpace : Nat -> Type -> Type
StateSpace n a = Vect n (Complex a)

||| Quantum observable type, n x n complex matrices
Op : Nat -> Type -> Type
Op n a = Matrix n n (Complex a)

||| Ket vector, a n x 1 matrix collumn
KetSpace : Nat -> Type -> Type
KetSpace n a = Matrix n 1 (Complex a)

||| Bra vector, a 1 x n matrix row
BraSpace : Nat -> Type -> Type
BraSpace n a = Matrix 1 n (Complex a)

||| Qubit state space type, 2^n dimensional Hilbert space
Qubit : Nat -> Type -> Type
Qubit n a = StateSpace (power 2 n) a

||| Qubit observable type
QubitOp : Nat -> Type -> Type
QubitOp n a = let m = power 2 n in Matrix m m (Complex a)

||| Qubit collumn vector type
QubitKet : Nat -> Type -> Type
QubitKet n a = let m = power 2 n in Matrix m 1 (Complex a)

||| Qubit row vector type
QubitBra : Nat -> Type -> Type
QubitBra n a = let m = power 2 n in Matrix 1 m (Complex a)



c0 : Num a => Complex a
c0 = 0 :+ 0

c1 : Num a => Complex a
c1 = 1 :+ 0

ci : Num a => Complex a
ci = 0 :+ 1

m1 : (Neg a, Num a) => Complex a
m1 = -1 :+ 0

mi : (Neg a, Num a) => Complex a
mi = 0 :+ -1

-- sqn : (Foldable t, Functor t) => t Amp -> Amp
-- sqn = sum' . map ((\x => conjugate x * x))

-- normalize : (Foldable t, Functor t) => t Amp -> t Amp
-- normalize xs = let n = sqn xs in map (map (\x => xn))
-- Can't resolve type class Functor f
-- normalize : Vect n

---- Relativistic types ----

Mink : Type
Mink = Vect 4 Amp

MinkR : Type
MinkR = Vect 4 Fl
