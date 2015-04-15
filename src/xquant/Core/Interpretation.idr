module xquant.Core.Interpretation

import xquant.Core.Types

%default total


||| Represents a mapping of a model (vector space) to
||| a physical system. Denoted by descriptive strings
data Interpretation : Nat -> Type where
  Interpret : Vect n String -> Interpretation n

dim : Interpretation n -> Nat
dim {n} i = n

Interp : Type
Interp = (n : Nat ** Interpretation n)

{-}
||| Representation of a possibly-composite quantum system
||| @ n the dimensionality of the physical system
data System : (n : Nat) -> List Interp -> Type where
  ||| Representation of a quantum system with a distinct interpretation
  Single : (i : Interpretation n) -> System n [i]
  ||| Extend an quantum system by tensor multiplying by another hilbert space
  Extend : (i : Interpretation n) -> System m -> System (n * m)

-}



qubit : Interpretation 2
qubit = Interpret ["Spin up", "Spin down"]


||| Type-safe representation of choice combinatorics
||| @ n total objects
||| @ m remaining unchosen
|||
||| For example this works fine:
|||````idris example
|||Choose FZ . Choose (FS FZ) $ (ChZero 2)
|||````
||| However both of these do not:
|||````idris example
|||Choose FZ . Choose FZ . Choose FZ $ (ChZero 2)
|||````
|||````idris example
|||Choose (FS FZ) . Choose FZ $ (ChZero 2)
|||````
data Choice : (n : Nat) -> (m : Nat) -> Type where
  ||| No Choices yet
  ChZero : (n : Nat) -> Choice n n
  |||
  Choose : (f : Fin (S m)) -> Choice n (S m) -> Choice n m
