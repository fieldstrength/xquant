module xquant.Core.Helicity

import xquant.Core.Types
import Data.Matrix.Numeric

%default total


---- Helicity type synonyms ----

Bispinor : Type
Bispinor = Matrix 2 2 Amp

Gamma : Type
Gamma = Matrix 4 4 Amp

---- Constant bispinors: Pauli matrices, antisym tensor ----

private i : Amp
i = 0 :+ 1

%access public

sx : Bispinor
sx = [[0,1],[1,0]]

sy : Bispinor
sy = [[0,i],[-i,0]]

sz : Bispinor
sz = [[1,0],[0,-1]]

ep : Bispinor
ep = [[0,-1],[1,0]]


---- Momentum bispinors σ(p) ----

||| Produce a bispinor from a Minkowski 4-vector
bispin : Mink -> Bispinor
bispin [e,px,py,pz] = (e  <#> Id)
                    + (px <#> sx)
                    + (py <#> sy)
                    + (pz <#> sz)


||| Produce a bispinor from a Minkowski 4-vector;
||| Upstairs spinor index (barred) version
bispin' : Mink -> Bispinor
bispin' [e,px,py,pz] = (e  <#> Id)
                     - (px <#> sx)
                     - (py <#> sy)
                     - (pz <#> sz)

||| Minkowski inner product
mink : Mink -> Mink -> Amp
mink (x0 :: xs) (y0 :: ys) = -(x0 * y0) + (xs <:> ys)

|||
eta : Gamma
eta = diag_ [-1,1,1,1]

gx : Matrix 4 4 Amp
gx = concatMatrix [[0,-sx],[sx,0]]

gy : Matrix 4 4 Amp
gy = concatMatrix [[0,-sy],[sy,0]]

gz : Matrix 4 4 Amp
gz = concatMatrix [[0,-sz],[sz,0]]

g0 : Matrix 4 4 Amp
g0 = concatMatrix {x=2} [[0,Id],[Id,0]]

||| Feynman slash: Dot a minkowski vector
||| into the gamma matrix vector
slash : Mink -> Matrix 4 4 Amp
slash [e,x,y,z] = (e <#> Id)
                + (x <#> gx)
                + (y <#> gy)
                + (z <#> gz)

||| 4 standard gamma matrices for D=4
gammas : Vect 4 Gamma
gammas = [g0,gx,gy,gz]


||| implicit conversion from Float to Complex Float
private implicit toCF : Fl -> Amp
toCF x = x :+ 0


g5 : Gamma
g5 = i <#> foldr1 (<>) gammas

||| Left-handed spinor projection
pL : Gamma
pL = 0.5 <#> (1 - g5)

||| Right-handed spinor projection
pR : Gamma
pR = 0.5 <#> (1 + g5)


||| Generate a vector from function
vecGen : (Fin n -> a) -> Vect n a
vecGen f = map f (fins _)

||| Generate a matrix from function
matGen : (Fin n -> Fin m -> a) -> Matrix n m a
matGen f = vecGen <$> vecGen f

||| Spin matrix
spin : Fin 4 -> Fin 4 -> Gamma
spin j k = i*(1/4) <#> index j gammas <<>> index k gammas
