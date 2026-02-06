# TODO.md: Phase 2 - Extreme Ray Construction & Verification

With the base infrastructure complete, we move to the core objective: constructing and proving the existence of **nontrivial extreme rays** for a discretized AQEI model.

## Objective
Construct an explicit polytope approximating the AQEI admissble set (by fixing a finite set of worldline constraints) and use Lean to **prove** that a specific point found by optimization is a vertex (extreme ray) of this polytope.

## Step 1: Optimization-Based Constraint Search (Mathematica) [Completed]
**Status:** Done via `mathematica/search.m`.
1. Generated 50 random constraints.
2. Solved LP to find a vertex `a` (minimizing energy/hitting bounds).
3. Exported numerical data (`vertex.json`).
4. **Outcome**: Found a valid vertex with 3 active AQEI constraints + box constraints.

## Step 2: Python Data Translation [Completed]
**Status:** Done via `tools/generate_lean_data.py`.
1. Implemented `tools/verify_vertex.py` to double-check the values.
2. Generated `lean/src/AQEI_Generated_Data.lean` containing the float values for Basis, Coefficients, and Active Constraints.

## Step 3: Lean Verification of Extremality
**Task:** Create `lean/src/VertexVerification.lean` to:
1. Import `AQEI_Generated_Data` and the coefficient model `AQEIFamilyInterface`.
2. Define `IsVertex (S : Set (Fin n → ℝ)) (v : Fin n → ℝ)`.
3. Prove that the exported `v` is indeed a vertex of the polytope defined by intersection of half-spaces `L_k \cdot x + B_k \ge 0`.
   - Strategy: Prove that the active constraints have full rank normals and intersect exactly at `v`.
   - **Note:** Since we are using Floats, this will be a "computationally verified" proof rather than an exact symbolic one, unless we switch to Rational arithmetic.

## Step 4: Final Theorem "Paper"
**Task:** Create a summary Lean file `lean/src/Theorems.lean` that collects the results:
- "The set of coefficients satisfying the discretized AQEI bounds is a closed, convex set."
- "The point `v` is an extreme point of this set."
- This formally establishes the "nontrivial extreme rays" property for the finite-dimensional approximation.

- Exploring specific AQEI bounds from QFT literature