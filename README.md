# LeanBCNF: Formal Verification of the BCNF Decomposition Algorithm in Lean

This repository builds upon the foundational formalization of relational algebra ([Rickerd1234/RelationalAlgebra](https://github.com/Rickerd1234/RelationalAlgebra)) to implement and verify **Relational Database Normalization Theory** in the Lean 4 proof assistant. This work forms the core formalization for the Master's thesis, *Formal Verification of the BCNF Decomposition Algorithm in Lean*, conducted at Eindhoven University of Technology (TU/e).

The primary objective of this project is to leverage dependent type theory to provide strict mathematical definitions and machine-checked proofs for functional dependencies, Armstrong's axioms, attribute closure computation, and the Boyce-Codd Normal Form (BCNF) decomposition algorithm, along with a *computable* and verified version of the final algorithm.

## Core Highlights

+ **Functional Dependencies & Closures**: Formalizes the semantics of FDs, proves the soundness and completeness of Armstrong's Axioms, and implements a verified, terminating attribute closure algorithm.

+ **Keys & Superkeys**: Establishes the equivalence between the semantic definitions of keys and their syntactic computations.

+ **Decomposition (Trees) & Losslessness**: Defines the conditions for lossless-join decompositions and provides the recursive data structures (Decomposition Trees) needed to represent them.

+ **Verified BCNF Algorithm**: Implements a standard BCNF decomposition algorithm mathematically (from the finite-set perspective) with end-to-end machine-checked guarantees.

+ **Computable Equivalence**: Implements a computable version of the BCNF decomposition algorithm from the sequence (list) perspective, whose losslessness and BCNF compliance are also verified.

## Documentation

With the support of [LeanArchitect](https://github.com/hanwenzhu/LeanArchitect) and [Lean blueprint](https://github.com/PatrickMassot/leanblueprint), we have generated online documentation for the definitions and theorems in the codebase, available on the [GitHub Pages](https://brandonw3612.github.io/LeanBCNF) associated with this repository.