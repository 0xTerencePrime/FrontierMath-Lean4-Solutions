# Formal Verification of the 5/8 Theorem in Lean 4

## Overview
This repository contains a complete formal proof of the 5/8 Theorem on Group Commutativity. This work serves as a verified solution for the Epoch AI FrontierMath Benchmark (Sample Set, Tier 4).

The primary objective of this project is to demonstrate the capability of Lean 4 and Mathlib in handling finite group theory and probabilistic bounds without relying on unproven axioms.

## Theorem Statement
For any finite group G, if the probability that two randomly chosen elements commute is strictly greater than 5/8, then G must be abelian.

Mathematically, we define the commuting probability cp(G) as:
cp(G) = |{(x, y) \in G \times G : xy = yx}| / |G|^2

The theorem states:
cp(G) > 5/8 \implies G is abelian.

## Implementation Details
- **Language**: Lean 4 (v4.15.0)
- **Library**: Mathlib4
- **Verification Status**: Fully verified. The proof contains no `sorry` placeholders and passes all linter checks.
- **Computation**: The solution includes a computational verification for the Dihedral Group D8 using `native_decide`, confirming that cp(D8) = 5/8 exactly.

## Mathematical Strategy
The formalization follows the standard group theoretic proof using the Class Equation:

1.  **Characterization via Conjugacy Classes**:
    We first establish that the commuting probability is equal to k(G)/|G|, where k(G) is the number of conjugacy classes in G.

2.  **Analysis of the Center**:
    We proceed by contradiction. Assuming G is non-abelian, we prove that the quotient group G/Z(G) cannot be cyclic. This implies that the index of the center, [G:Z(G)], must be at least 4.

3.  **Bounding the Probability**:
    Using the Class Equation and the bound on the center's index, we derive an upper bound for the sum of the cardinalities of centralizers. We utilize the `nlinarith` tactic to handle the algebraic inequalities, proving that the probability cannot exceed 5/8 for non-abelian groups.

## Build Instructions
To compile and verify the proofs on a local machine:

1.  Clone the repository:
    ```bash
    git clone https://github.com/0xTerencePrime/FrontierMath-Lean4-Solutions.git
    ```

2.  Retrieve Mathlib cache (required for macOS/Linux builds):
    ```bash
    lake exe cache get
    ```

3.  Build the project:
    ```bash
    lake build
    ```

4.  Run the linter to verify code quality:
    ```bash
    lake exe runLinter
    ```

## Verification Evidence
A screenshot of the successful build output and the "No goals" state in the Lean Infoview is included in this repository as `proof_screenshot.jpg`.

## Contact
**Mathlib Contributor**
Specializing in formal verification for mathematical benchmarks and cryptographic circuits.
