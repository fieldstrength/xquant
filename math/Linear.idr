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


conjugate : Group a => Complex a -> Complex a
conjugate (x :+ y) = x :+ (inverse y)


data AntiLinearMap : (Group a, Module (Complex a) b) => (b -> b) -> Type where
  IsAntiLinearMap : (Group a, Module (Complex a) b) => 
                    (f : b -> b) ->
                    f ((r <#> x) <+> (s <#> y)) = (Linear.conjugate r) <#> (f x) <+> ((Linear.conjugate s) <#> (f y)) ->
                    AntiLinearMap f


data SesquiLinearMap : (Group a, Module (Complex a) b) => (b -> b -> b) -> Type where
  IsSesquiLinearMap : (Group a, Module (Complex a) b) => 
                      (f : b -> b -> b) ->
                      f ((r <#> x) <+> (s <#> y)) z = r <#> (f x z) <+> (s <#> (f y z)) ->
                      f z ((r <#> x) <+> (s <#> y)) = (Linear.conjugate r) <#> (f z x) <+> ((Linear.conjugate s) <#> (f z y)) ->
                      SesquiLinearMap f
