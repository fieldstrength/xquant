module xquant.Math.Set

import public Data.Vect

%default total

||| A vector of unique elements
data Set : Vect n a -> Type where
  Nil  : Set []
  (::) : Not (Elem x xs) -> Set xs -> Set (x :: xs)

||| Elements of a type
data HasElements : (t : Type) -> (v : Vect n t) -> Type where
  MkHas : {v : Vect n t} ->
          Set v ->
          ((x : t) -> Elem x v) ->
          HasElements t v

data Cardinality : (t : Type) -> Nat -> Type where
  Cardinal : {v : Vect n t} -> HasElements t v -> Cardinality t n


noElem : Elem x [] -> Void
noElem Here impossible

---- Example: Bool ----

notElemTF : Elem True [False] -> Void
notElemTF Here impossible
notElemTF (There x) = noElem x

setFalse : Set [False]
setFalse = noElem :: []

set1 : (x : a) -> Set [a]
set1 x = noElem :: []


setTrueFalse : Set [True, False]
setTrueFalse = notElemTF :: setFalse

boolHas : HasElements Bool [True,False]
boolHas = MkHas setTrueFalse (\b => case b of
                                         True  => Here
                                         False => There Here)

boolHasTwo : Cardinality Bool 2
boolHasTwo = Cardinal boolHas
