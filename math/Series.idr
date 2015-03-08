module Series

import Data.Vect

import math.NNat
import math.NVect


%default total


----------------------------------------------------------------------
--                             Stream ops
----------------------------------------------------------------------

||| Map a function over a stream
comap : (a -> b) -> Stream a -> Stream b
comap f (x::xs) = f x :: (Delay $ comap f xs)

||| Zip two streams with supplied function
cozipWith : (a -> b -> c) -> Stream a -> Stream b -> Stream c
cozipWith f (x::xs) (y::ys) = f x y :: (Delay $ cozipWith f xs ys)

nats : Stream Nat
nats = iterate S Z

take' : (n : Nat) -> Stream a -> Vect n a
take' Z     s       = []
take' (S n) (x::xs) = x :: (take' n xs)

discard : Nat -> Stream a -> Stream a
discard Z     s = s
discard (S n) s = tail $ discard n s

dropLast : Vect (S n) a -> Vect n a
dropLast [x]        = []
dropLast (x::y::ys) = (x :: (dropLast $ y :: ys))

prepend : Vect n a -> Stream a -> Stream a
prepend []      s = s
prepend (x::xs) s = prepend (dropLast $ x :: xs) $ (last $ x :: xs) :: s

----------------------------------------------------------------------
--                          Power series
----------------------------------------------------------------------

||| Representation of a power series
data PowerSeries : Type -> Type where
  ||| Represent a power series by specifying the coefficients
  ||| @ f the coefficient function
  Series : RingWithUnity a => (f : Nat -> a) -> PowerSeries a

||| Stream of values representing the summands of the series
||| @ x the argument of the polynomial
interpSeries : PowerSeries a -> (x : a) -> Stream a
interpSeries (Series f) x = cozipWith (<.>) (comap f nats) (iterate (<.> x) unity)

||| Define a power series by a stream of coefficients
coeffSeries : RingWithUnity a => Stream a -> PowerSeries a
coeffSeries s = Series (\n => index n s)

||| Evaluate a series by summing a finite-length sample
approx : Semigroup a => NNat -> PowerSeries a -> a -> a
approx (nS n) series x = NVect.sum . fromVect . take' (S n) $ interpSeries series x

