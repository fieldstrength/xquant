module Linear

import Data.Complex
import Data.Matrix

data Linear : Semigroup a => (a -> a) -> Type where
  IsLinear : Semigroup a => (f : a -> a) -> 
             f (x <+> y) = f x <+> (f y) ->
             Linear f


data LinearMap : Module a b => (b -> b) -> Type where
  IsLinearMap : Module a b => 
                (f : b -> b) -> 
                f ((r <#> x) <+> (s <#> y)) = r <#> (f x) <+> (s <#> (f y)) ->
                LinearMap f


||| Complex conjugate
conj : Group a => Complex a -> Complex a
conj (x :+ y) = x :+ (inverse y)


data AntiLinearMap : (Group a, Module (Complex a) b) => (b -> b) -> Type where
  IsAntiLinearMap : (Group a, Module (Complex a) b) => 
                    (f : b -> b) ->
                    f ((r <#> x) <+> (s <#> y)) = (conj r) <#> (f x) <+> ((conj s) <#> (f y)) ->
                    AntiLinearMap f


data SesquiLinearMap : (Group a, Module (Complex a) b) => (b -> b -> b) -> Type where
  IsSesquiLinearMap : (Group a, Module (Complex a) b) => 
                      (f : b -> b -> b) ->
                      f ((r <#> x) <+> (s <#> y)) z = r <#> (f x z) <+> (s <#> (f y z)) ->
                      f z ((r <#> x) <+> (s <#> y)) = (conj r) <#> (f z x) <+> ((conj s) <#> (f z y)) ->
                      SesquiLinearMap f


data EigenPair : Module a b => (b -> b) -> b -> a -> Type where
  IsEigenPair : Module a b => 
                (f : b -> b) ->
                (v : b) -> 
                (r : a) ->
                f v = r <#> v ->
                EigenPair f v r



{-
Type checking ./math/Linear.idr
./math/Linear.idr:11:21:
When elaborating type of Linear.linearMapTransitive:
Can't resolve type class Semigroup a2

for :

linearTransitive : Semigroup a => {a : Type} -> (f : a -> a) -> 
                                  Linear f ->
                                  (g : a -> a) ->
                                  Linear g ->
                                  Linear (g . f)
linearTransitive f (IsLinear f feq) g (IsLinear g geq) = IsLinear (g . f) ?w

linearMapTransitive : Semigroup a =>
                      (f : b -> b) ->
                      LinearMap f
                      (g : b -> b) ->
                      LinearMap g ->
                      LinearMap (g . f)
-}



