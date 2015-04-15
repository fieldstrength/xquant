module math.Epsilon

import xquant.Core.Types

%default total


class Epsilon a where
  infinitessimal : a -> Bool

instance Epsilon Fl where
  infinitessimal x = abs x < 0.00000001

instance Epsilon Amp where
  infinitessimal x = realPart (abs x) < 0.00000001

instance Epsilon (Vect n Fl) where
  infinitessimal = all infinitessimal

instance Epsilon (Vect n Amp) where
  infinitessimal = all infinitessimal

instance Epsilon (Vect n (Vect m Fl)) where
  infinitessimal = all infinitessimal

instance Epsilon (Vect n (Vect m Amp)) where
  infinitessimal = all infinitessimal

sumSq : (Functor t, Foldable t, Neg a) => t a -> a
sumSq = sum . map ((\n => n*n) . abs)

data Real : Amp -> Type where
  IsReal : (z : Amp) -> {auto isinf : infinitessimal (imagPart z) = True} -> Real z

{-
*quantum> :r
Type checking ./math/Epsilon.idr
./math/Epsilon.idr:20:10:
Overlapping instance: Epsilon (Complex Double) already defined

approximates : Epsilon
-}

{-}
--instance (Neg a, Epsilon a) => Epsilon (Vect n a) where
--  infinitessimal = infinitessimal . sumSq

--data Infinitessimal : Type where
--  Infini : Epsilon a => (x : a) -> {auto isep : infinitessimal x = True} -> Infinitessimal x

-- data Unitary : (mat : Matrix n n (Complex Float)) -> Type where
--  IsUnitary : {prf : mat <> dagger )}
-}
