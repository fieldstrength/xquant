module xquant.Graph.Feynman

import xquant.Graph.Marked
import Control.Algebra

%default total


||| Fixed interaction order scalar particle graph
||| @ n number of line endpoints attached to each vertex (interaction order)
||| @ l number of lines
||| @ v number of vertices
||| @ m which line endpoints are attached to vertices
data ScalarGraph : (n : Nat) ->
                   (l : Nat) ->
                   (v : Nat) ->
                   (m : Marks (2*l) j) ->
                   Type where
  Grf : (n : Nat) ->
        (l : Nat) ->
        ScalarGraph n l Z allO
  vertex : (x : Marks (2*l) n) ->
           {y : Marks (2*l) j} ->
           (c : Compat x y) ->
           ScalarGraph n l v y ->
           ScalarGraph n l (S v) (markAdd c)

||| The number of external lines is the number of endpoints not connected to vertices
external : ScalarGraph n p v m -> Nat
external {n} {p} {v} g = 2*p `minus` n*v


-- example: the interaction vertex in phi^3 theory
phi3vertex : ScalarGraph 3 3 1 [O,X,O,X,O,X]
phi3vertex = vertex [O,X,O,X,O,X]
                    (ComOO $ ComXO $ ComOO $ ComXO $ ComOO $ ComXO ComZero)
                    (Grf 3 3)


||| Directed Graph with fixed number of line-endpoints per vertex
||| @ n number of line endpoints attached to each vertex (interaction order)
||| @ l number of lines
||| @ v number of vertices
||| @ m which line endpoints are attached to vertices
||| @ h which line arrows are reversed
data Digraph : (n : Nat) ->
               (l : Nat) ->
               (v : Nat) ->
               (m : Marks (2*l) j) ->
               (h : Marks l k) ->
               Type where
  DiGrf : (n : Nat) ->
          (l : Nat) ->
          Digraph n l Z empty (empty_ l)
  DiVrtx : (x : Marks (2*l) n) ->
           {y : Marks (2*l) j} ->
           (c : Compat x y) ->
           Digraph n l v y r ->
           Digraph n l (S v) (markAdd c) r



||| Very basic particle content. Should dramatically generalize from here
||| Here only takes number of scalars and fermions
data ParticleContent = Particles Nat Nat

data VertexType : Nat -> Type where
   VertType : (b : Nat) -> (f : Nat) -> VertexType (n + 2*m)


-- data SFPropagator : Nat -> Type where
-- SFProp : Marks 2

||| Directed Graph with fixed number of line-endpoints per vertex
||| @ s scalar lines
||| @ f fermion lines
||| @ v number of vertices
||| @ sm which scalar line endings are attached to vertices
||| @ fb which fermionic line _beginnings_ are attached to vertices
||| @ fe which fermionic line _end_points are attached to vertices
data SimpScalarFermion : (s : Nat) ->
                         (f : Nat) ->
                         (v : Nat) ->
                         (sm : Marks (2*s) i) ->
                         (fb : Marks f j) ->
                         (fe : Marks f j) -> Type where
  SFGrf : (s,f : Nat) ->
          SimpScalarFermion s f Z empty (empty_ _) (empty_ _)
  SFVrtx : SimpScalarFermion s f v sm fb fe ->
           {x : Marks (2*s) 1} ->
           {y : Marks f 1} ->
           {z : Marks f 1} ->
           (c : Compat x sm) ->
           (d : Compat y fb) ->
           (e : Compat z fe) ->
           SimpScalarFermion s f (S v) (markAdd c) (markAdd d) (markAdd e)
