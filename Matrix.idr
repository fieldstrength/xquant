
module Matrices

infixl 1 \+\  -- Vector plus  (V begins with \)
infixl 1 /+/  -- Matrix plus  (M begins with /)
infixl 1 \-\  -- Vector minus
infixl 1 /-/  -- Matrix minus
infixr 2 <.>
infixr 2 <<>>
infixr 2 >><<
infixr 4 </>
infixr 5 <>
infixr 7 <&>
infixr 7 \&\

-------------------------------------------------------------------------------------------
--                                      Vector Stuff
-------------------------------------------------------------------------------------------


||| Dot product between numerical vectors
(<.>) : Num a => Vect n a -> Vect n a -> a
(<.>) w v = sum (zipWith (*) w v)

||| Scale a numerical vector by a scalar of the appropriate type
scale : Num a => Vect n a -> a -> Vect n a
scale v s = map (* s) v

||| Make an n-dimensional vector from a function of Fin-n
vectorMaker : {n : Nat} -> (Fin n -> a) -> Vect n a
vectorMaker {n} f = map f (allN n) where
  allN : (n : Nat) -> Vect n (Fin n)
  allN Z     = Nil
  allN (S n) = fZ :: (map fS $ allN n)

||| Vector addition
Vector.(\+\) : Num a => Vect n a -> Vect n a -> Vect n a
Vector.(\+\) v w = zipWith (+) v w

||| Vector subtraction
Vector.(\-\) : Num a => Vect n a -> Vect n a -> Vect n a
Vector.(\-\) v w = zipWith (-) v w


||| Tensor product for numerical vectors
ox : Num a => Vect n a -> Vect m a -> Vect (n * m) a
ox {n} {m} q w = zipWith (*) (oextend m q) (orep n w) where
  orep : {N : Nat} -> (M : Nat) -> Vect N a -> Vect (M * N) a
  orep M Q = concat $ replicate M Q
  oextend : (j : Nat) -> Vect k a -> Vect (k * j) a
  oextend {k} j w = concat $ map (replicate j) w

(\&\) : Num a => Vect n a -> Vect m a -> Vect (n * m) a
(\&\) = ox


||| Standard basis vector with one nonzero entry and the numeric typeclass left unfixed
sBasis : Num a => (n : Nat) -> Nat -> Vect n a
sBasis n m = reverse $ sbasis n m where
  sbasis Z     _     = Nil
  sbasis (S k) (S j) = let s = if j == k then (product Vect.Nil) else (sum Vect.Nil) in s :: (sbasis k (S j))

sqNorm : Num a => Vect n a -> a
sqNorm v = sum $ map ((\x => x*x) . abs) v

norm : Vect n Float -> Float
norm v = prim__floatSqrt $ sqNorm v

-------------------------------------------------------------------------------------------
--                                      Matrix Stuff
-------------------------------------------------------------------------------------------


||| Matrix with n cols and m rows
Matrix : Nat -> Nat -> Type -> Type
Matrix n m a = Vect n (Vect m a)


||| Gets the specified row of a matrix. For cols use the vector function 'index'
getRow : Fin m -> Matrix n m a -> Vect n a
getRow fm q = map (index fm) q

||| Deletes the specified row of a matrix. For cols use the vector function 'deleteAt'
deleteRow : Fin (S m) -> Matrix n (S m) a -> Matrix n m a
deleteRow f m = map (deleteAt f) m

||| Matrix element at specified row and collumn indices
atRowCol : Fin m -> Fin n -> Matrix n m a -> a
atRowCol fm fn m = index fm (index fn m)


Matrix.(/+/) : Num a => Matrix n m a -> Matrix n m a -> Matrix n m a
Matrix.(/+/) = zipWith Vector.(\+\)

Matrix.(/-/) : Num a => Matrix n m a -> Matrix n m a -> Matrix n m a
Matrix.(/-/) = zipWith Vector.(\-\)


||| Numerical matrix times scalar of the appropriate type
mScale : Num a => a -> Matrix n m a -> Matrix n m a
mScale s m = map (map (* s)) m

ScalarMat.(*) : Num a => a -> Matrix n m a -> Matrix n m a
ScalarMat.(*) s m = mScale s m 

MatScalar.(*) : Num a => Matrix n m a -> a -> Matrix n m a
MatScalar.(*) m s = mScale s m 


||| Matrix times a vector
(</>) : Num a => Matrix n m a -> Vect n a -> Vect m a
(</>) m v = vectorMaker (rowApply m v) where
  rowApply : Num b => {N,M : Nat} -> Matrix N M b -> Vect N b -> Fin M -> b
  rowApply mat v f = (getRow f mat) <.> v

||| Matrix multiplication
(<>) : Num a => Matrix k m a -> Matrix n k a -> Matrix n m a
(<>) m1 m2 = map ((</>) m1) m2


||| Tensor product for numerical matrices
(<&>) : Num a => Matrix w1 h1 a -> Matrix w2 h2 a -> Matrix (w1 * w2) (h1 * h2) a
(<&>) m1 m2 = zipWith ox (stepOne m1 m2) (stepTwo m1 m2) where
  stepOne : Matrix w1 h1 a -> Matrix w2 h2 a -> Matrix (w1 * w2) h1 a
  stepOne {w2} m1 m2 = concat $ map (replicate w2) m1
  stepTwo : Matrix w1 h1 a -> Matrix w2 h2 a -> Matrix (w1 * w2) h2 a
  stepTwo {w1} m1 m2 = concat $ (Vect.replicate w1) m2


||| Cast a vector from a standard Vect to a proper n x 1 matrix 
col : Num a => Vect n a -> Matrix 1 n a
col v = [v]

||| Cast a row from a standard Vect to a proper 1 x n matrix 
row : Num a => Vect n a -> Matrix n 1 a
row v = map (\x => [x]) v


||| N-dimensional identity matrix for any numeric typeclass
idN : Num a => (d : Nat) -> Matrix d d a
idN d = map (\n => sBasis d $ finToNat n) $ allN d where
  allN : (n : Nat) -> Vect n (Fin n)
  allN Z     = Nil
  allN (S n) = fZ :: (map fS $ allN n)


||| Matrix Commutator
(<<>>) : Num a => Matrix n n a -> Matrix n n a -> Matrix n n a
(<<>>) m1 m2 = (m1 <> m2) /-/ (m2 <> m1)

||| Matrix Anti-Commutator
(>><<) : Num a => Matrix n n a -> Matrix n n a -> Matrix n n a
(>><<) m1 m2 = (m1 <> m2) /+/ (m2 <> m1)
