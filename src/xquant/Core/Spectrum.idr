module xquant.Core.Spectrum

import public xquant.Core.Types
import public xquant.Core.NonZero
import Data.Matrix.Algebraic


%default total


data SysType = Finite Nat | Infinite

||| Spectrum – list of energies – for
||| a finite-dimensional system
data FSpectrum : Nat -> Type where
  FSpect : Vect n Fl -> FSpectrum n

||| Finite system degeneracy, i.e.,
||| state multiplicity by energy level
data FDegen : Nat -> Type where
  FDeg : {v : Vect n Nat} -> NVect v -> FDegen n

size : FDegen n -> Nat
size (FDeg {v} _) = sum v

rep : FDegen n -> Type
rep fd = StateSpace (size fd) Amp

data FSystem : Nat -> Type where
  FSys : (fd : FDegen n) ->
         FSpectrum n ->
         rep fd ->
         FSystem n

||| Infinite system spectrum
data ISpectrum = ISpect (Nat -> Fl)

||| Infinite system degeneracy
||| (state multiplicity by energy level)
data IDegen : Type where
  IDeg : (Nat -> NonZ) -> IDegen
