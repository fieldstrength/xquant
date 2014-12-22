module Graphs

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
                   (m : Marks (2*l) f) -> 
                   Type where
  grfInit : (n : Nat) ->
            (l : Nat) ->
            ScalarGraph n l Z (getProof $ fromV $ replicate (2*l) O)
  vertex : (x : Marks (2*l) n) ->
           {y : Marks (2*l) j} ->
           (c : Compat x y) ->
           ScalarGraph n l v y ->
           ScalarGraph n l (S v) (markAdd x y c)

||| The number of external lines is the number of endpoints not connected to vertices
external : ScalarGraph n p v m -> Nat
external {n} {p} {v} g = 2*p - n*v


-- example: the interaction vertex in phi^3 theory
phi3vertex : ScalarGraph 3 3 1 $ getProof $ fromV [O,X,O,X,O,X]
phi3vertex = vertex (getProof $ fromV [O,X,O,X,O,X]) 
                    (comOO $ comXO $ comOO $ comXO $ comOO $ comXO $ comZero) $ 
                    grfInit 3 3