module xquant.Math.Hilbert

import xquant.Core.Types
import Data.Matrix
import Data.Complex

-- Normalize
normalize : StateSpace n Float -> StateSpace n Float
normalize q = map (\(r :+ i) => (r / (sqrt sqn)) :+ (i / (sqrt sqn))) q where
   sqn : Double
   sqn = sum $ map ((\x => x*x) . magnitude) q

conjugate : (Num a , Neg a) => Complex a -> Complex a
conjugate (r :+ i) = r :+ -i

-- Infix Hilbert inner product
--   should be more general, but no official declaration for Num a => Num (Complex a)
||| Hilbert Inner product
(<|>) : StateSpace n Float -> StateSpace n Float -> Complex Float
(<|>) q w = sum $ zipWith (*) (map Complex.conjugate q) w


-- Hermitian conjugate (adjoint) on complex matrices
dagger : (Num a , Neg a) => Matrix n m (Complex a) -> Matrix m n (Complex a)
dagger h = map (map Hilbert.conjugate) $ transpose h

-- Complex number divide
(/) : Complex Float -> Complex Float -> Complex Float
(/) (a:+b) (c:+d) = let real = (a*c+b*d)/(c*c+d*d)
                        imag = (b*c-a*d)/(c*c+d*d)
                    in  (real :+ imag)
