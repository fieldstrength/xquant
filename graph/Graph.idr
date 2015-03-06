module Graphs

import Data.Fin

import graph.Marked


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
        ScalarGraph n l Z (getProof $ fromV $ replicate (2*l) O)
  vertex : (x : Marks (2*l) n) ->
           {y : Marks (2*l) j} ->
           (c : Compat x y) ->
           ScalarGraph n l v y ->
           ScalarGraph n l (S v) (markAdd c)

||| The number of external lines is the number of endpoints not connected to vertices
external : ScalarGraph n p v m -> Nat
external {n} {p} {v} g = 2*p - n*v


-- example: the interaction vertex in phi^3 theory
phi3vertex : ScalarGraph 3 3 1 $ getProof $ fromV [O,X,O,X,O,X]
phi3vertex = vertex (getProof $ fromV [O,X,O,X,O,X])
                    (comOO $ comXO $ comOO $ comXO $ comOO $ comXO comZero)
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
          Digraph n l Z (getProof $ fromV $ replicate (2*l) O) (getProof $ fromV $ replicate l O)
  DiVrtx : (x : Marks (2*l) n) ->
           {y : Marks (2*l) j} ->
           (c : Compat x y) ->
           Digraph n l v y r ->
           Digraph n l (S v) (markAdd c) r
