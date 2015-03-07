quantum
=======

Dependently-typed structures for quantum physics in Idris

This is a set of Idris libraries I'm developing for a variety of tasks related to quantum physics. Most of them are directly relevant for the main program (in development) that's intended to perform basic simulations and calcuations of quantum systems, both infinite and finite-dimensional. Some parts are more tangentially related and may be factored out to independent projects.

This requires Idris 0.9.17 or current HEAD.

---

#### Sigmas
Data types representing the quantum operators of the _n_-qubit state space, and functions on them, especially implementing their algebra.

#### SigKets
Data types for _n_-qubit state vectors, and functions involving both vectors and operators. In particular, we can calculate outcome probabilities and expectation values for any observables.

#### Spinor
Writing down a field theory for fermions requires a representation of the gamma matrix algebra. In even dimensions _(d = 2k + 2)_ this is a set of _d_ square matrixes with size _2^(k+1)_. The next odd-dimensional representation is formed by adding an additional matrix of the same size, corresponding to the product of all the others. We implement functions to recursively define gamma matrices of arbitrary dimension starting with _d = 2_. These numerical properties are enforced by the type system.

#### Marked
Data type `Marks` representing the number of ways to choose _n_ objects from a set of _m_, along with related functions and proofs. Used to make `ScalarGraph`s.

#### Graph
Data type for correct-by-construction Feynman graph topologies with a fixed interaction order, i.e. a fixed number of line-endpoints connected to each vertex.

#### Hilbert
Various basic functions and type-level functions for quantum systems.

#### NNat
Data type for nonzero natural numbers, which are needed/helpful for defining `Rational` among other things. Basic functions and typeclass instances are provided. They're built from a standard `Nat` to take advantage of its special optimization.

#### Rational
Data type for rational numbers, using the Idris base library integer `ZZ` for a numerator and a `NNat` as a denominator. We define the `Quotient` class for data types that are interpreted as being defined _up to an equivalence class_, and instantiate `Rational` under this class. There's also a data type for positive rationals, called `Fraction`.
