module xquant.Core.NonZero

import Data.Vect

%default total

data NonZero : Nat -> Type where
  NZ : {k : Nat} -> NonZero (S k)

||| works but takes a while when N > ~1000
partial nonzero : (n : Nat) -> NonZero n
nonzero (S k) = NZ

NonZ : Type
NonZ = (n : Nat ** NonZero n)

||| Vector of Non-zero naturals
data NVect : (v : Vect n Nat) -> Type where
  Nil  : NVect []
  (::) : (n : Nat) -> NVect v -> {auto nz : NonZero n} -> NVect (n :: v)

partial
vtov : (v : Vect n Nat) -> NVect v
vtov [] = []
vtov ((S k)::ns) = S k :: (vtov ns)
