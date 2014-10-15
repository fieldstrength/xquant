
module Matrix


%default total


infixl 1 \+\  -- Vector plus  (mnemonic: V begins with '\')
infixl 1 /+/  -- Matrix plus  (          M begins with '/')
infixl 1 \-\  -- Vector minus
infixl 1 /-/  -- Matrix minus
infixr 2 <.>  -- Vector dot product
infixr 2 <<>> -- Matrix commutator
infixr 2 >><< -- Matrix anticommutator
infixl 3 <\>  -- row times a matrix
infixr 4 </>  -- matrix times a collumn
infixr 5 <>   -- matrix multiplication 
infixr 7 \&\  -- vector tensor product
infixr 7 <&>  -- matrix tensor product

---------------------------------------------------------------
--                      Vector Stuff
---------------------------------------------------------------

||| Dot product between numerical vectors
(<.>) : Num a => Vect n a -> Vect n a -> a
(<.>) w v = sum (zipWith (*) w v)

||| Scale a numerical vector by a scalar of the appropriate type
scale : Num a => Vect n a -> a -> Vect n a
scale v s = map (* s) v

||| Vector addition
(\+\) : Num a => Vect n a -> Vect n a -> Vect n a
(\+\) v w = zipWith (+) v w

||| Vector subtraction
(\-\) : Num a => Vect n a -> Vect n a -> Vect n a
(\-\) v w = zipWith (-) v w

||| Tensor multiply for numerical vectors
ox : Num a => Vect n a -> Vect m a -> Vect (n * m) a
ox {n} {m} q w = zipWith (*) (oextend m q) (orep n w) where
  orep : {N : Nat} -> (M : Nat) -> Vect N a -> Vect (M * N) a
  orep M Q = concat $ replicate M Q
  oextend : (j : Nat) -> Vect k a -> Vect (k * j) a
  oextend {k} j w = concat $ map (replicate j) w

(\&\) : Num a => Vect n a -> Vect m a -> Vect (n * m) a
(\&\) = ox

zero : Num a => {n : Nat} -> Vect n a
zero {n} = replicate n (fromInteger 0)

||| Standard basis vector with one nonzero entry, numeric typeclass left unfixed
basis : Num a => {n : Nat} -> (Fin n) -> Vect n a
basis i = replaceAt i (fromInteger 1) zero

sqNorm : Num a => Vect n a -> a
sqNorm v = sum $ map ((\x => x*x) . abs) v

norm : Vect n Float -> Float
norm v = prim__floatSqrt $ sqNorm v


---------------------------------------------------------------
--                      Matrix Stuff
---------------------------------------------------------------

||| Matrix with n rows and m collumns
Matrix : Nat -> Nat -> Type -> Type
Matrix n m a = Vect n (Vect m a)


||| Gets the specified collumn of a matrix. For rows use the vector function 'index'
getCol : Fin m -> Matrix n m a -> Vect n a
getCol fm q = map (index fm) q

||| Deletes the specified collumn of a matrix. For rows use the vector function 'deleteAt'
deleteCol : Fin (S m) -> Matrix n (S m) a -> Matrix n m a
deleteCol f m = map (deleteAt f) m

||| Matrix element at specified row and collumn indices
atRowCol : Fin n -> Fin m -> Matrix n m a -> a
atRowCol f1 f2 m = index f2 (index f1 m)

||| Matrix addition
(/+/) : Num a => Matrix n m a -> Matrix n m a -> Matrix n m a
(/+/) = zipWith (\+\)

||| Matrix subtraction
(/-/) : Num a => Matrix n m a -> Matrix n m a -> Matrix n m a
(/-/) = zipWith (\-\)


||| Numerical matrix times scalar of the appropriate type
mScale : Num a => a -> Matrix n m a -> Matrix n m a
mScale s m = map (map (* s)) m

ScalarMat.(*) : Num a => a -> Matrix n m a -> Matrix n m a
ScalarMat.(*) s m = mScale s m 

MatScalar.(*) : Num a => Matrix n m a -> a -> Matrix n m a
MatScalar.(*) m s = mScale s m 


||| Matrix times a collumn vector
(</>) : Num a => Matrix n m a -> Vect m a -> Vect n a
(</>) m v = map (v <.>) m

||| Matrix times a row vector
(<\>) : Num a => Vect n a -> Matrix n m a -> Vect m a
(<\>) r m = map (r <.>) $ transpose m


||| Matrix Multiplication
(<>) : Num a => Matrix n k a -> 
                Matrix k m a -> 
                Matrix n m a
(<>) m1 m2 = map (<\> m2) m1


||| Tensor multiply for numerical matrices
(<&>) : Num a => Matrix h1 w1 a -> Matrix h2 w2 a -> Matrix (h1 * h2) (w1 * w2) a
(<&>) m1 m2 = zipWith ox (stepOne m1 m2) (stepTwo m1 m2) where
  stepOne : Matrix h1 w1 a -> Matrix h2 w2 a -> Matrix (h1 * h2) w1 a
  stepOne {h2} m1 m2 = concat $ map (replicate h2) m1
  stepTwo : Matrix h1 w1 a -> Matrix h2 w2 a -> Matrix (h1 * h2) w2 a
  stepTwo {h1} m1 m2 = concat $ (Vect.replicate h1) m2


||| Cast a vector from a standard Vect to a proper n x 1 matrix 
col : Vect n a -> Matrix n 1 a
col v = map (\x => [x]) v

||| Cast a row from a standard Vect to a proper 1 x n matrix 
row : Vect n a -> Matrix 1 n a
row r = [r]

||| All finite numbers up to the given bound
allN : (n : Nat) -> Vect n (Fin n)
allN Z     = Nil
allN (S n) = fZ :: (map fS $ allN n)

||| d-dimensional identity matrix for unspecified numeric typeclass
Id : Num a => {d : Nat} -> Matrix d d a
Id {d} = map (\n => basis n) $ allN d


||| Matrix Commutator
(<<>>) : Num a => Matrix n n a -> Matrix n n a -> Matrix n n a
(<<>>) m1 m2 = (m1 <> m2) /-/ (m2 <> m1)

||| Matrix Anti-Commutator
(>><<) : Num a => Matrix n n a -> Matrix n n a -> Matrix n n a
(>><<) m1 m2 = (m1 <> m2) /+/ (m2 <> m1)