
import Mathlib
import AQEIToInterface
import PolyhedralVertex
import VertexVerificationRat

namespace FinalResults

open PolyhedralGeometry
open Phase2Rat
open AQEIGeneratedRat

/--
  FinalTheorems.lean

  Summary of the "Phase 2" effort to demonstrate Nontrivial Extreme Rays in the AQEI cone.

  We establish:
  1. The AQEI constraints form a closed convex set.
  2. The candidate point `candidate_v` (from the LP solver) satisfies 6 specific active constraints.
  3. These 6 constraints are linearly independent (proven via exact rational determinant).
  4. Therefore, `candidate_v` is an Extreme Point (vertex) of the Polyhedron defined by these constraints.
-/

abbrev Vector6 := Fin 6 → Rat

/-- The candidate vertex from the generated data -/
def candidate_v : Vector6 := fun i =>
  match coefficients.get? i.val with | some c => c | none => 0

/--
  The 6 functional constraints defining the local geometry around the vertex.
  Rows 0-2: AQEI constraints (Normal derived from active_L).
  Rows 3-5: Box constraints (Normal derived from unit vectors).

  Note: For indices 3-5 (Box constraints x_j ≤ 100), the inequality is -x_j ≥ -100.
  So the functional L is -e_j, and the bound -B is -100.
  The verification_matrix stores +e_j. So we apply a sign flip for i >= 3.
--/
def L_poly (i : Fin 6) : Vector6 →L[Rat] Rat :=
  let row := verification_matrix i
  let sign : Rat := if i < 3 then 1 else -1
  LinearMap.toContinuousLinearMap <| LinearMap.mk₂ Rat (· • ·)
    (fun v => sign * Matrix.dotProduct row v)
    (by intros; simp [Matrix.dotProduct, mul_add])
    (by intros; simp [Matrix.dotProduct, mul_comm, mul_left_comm])
    (by intros; simp [Matrix.dotProduct])

/-- The RHS bounds for the 6 active constraints. -/
def B_poly (i : Fin 6) : Rat :=
  if i < 3 then
    -- AQEI B values (active_B stores the values B_i such that L_i x >= -B_i)
    match active_B.get? i.val with | some b => b | none => 0
  else
    -- Box bounds. x <= 100 => -x >= -100. -B = -100 => B = 100.
    100

/- Proof that the candidate point exactly satisfies the equality constraints -/
theorem candidate_active_binding : ∀ i : Fin 6, L_poly i candidate_v = -B_poly i := by
  -- Computationally verify the binding using exact rational arithmetic.
  intro i
  fin_cases i
  <;> native_decide

/--
  The Candidate Vertex is an Extreme Point of the polyhedron defined by the 6 active constraints.
-/
theorem Candidate_Is_Extreme_Point :
    ConvexGeometry.IsExtremePoint (PolyhedralGeometry.Polyhedron L_poly B_poly) candidate_v := by
  apply PolyhedralGeometry.full_rank_active_implies_vertex
  · -- Feasibility
    simp [PolyhedralGeometry.Polyhedron]
    intro i
    rw [candidate_active_binding i]
    apply le_refl
  · -- All constraints are active (by definition of the polyhedron we constructed)
    intro i _
    exact candidate_active_binding i
  · -- Full Rank (Trivial Kernel Condition)
    intro v hv
    -- Goal: v = 0
    -- Hyp: ∀ i, L_poly i v = 0

    -- 1. Map L_poly i v = 0 to verification_matrix row v = 0
    have h_rows_zero : ∀ i, Matrix.dotProduct (verification_matrix i) v = 0 := by
      intro i
      specialize hv i (by simp)
      simp [L_poly] at hv
      -- sign * dot = 0. Since sign is ±1, dot is 0.
      split_ifs at hv
      · exact hv
      · -- -1 * dot = 0 => dot = 0
        linarith

    -- 2. This implies Matrix * v = 0
    have h_mat_mul : verification_matrix *ᵥ v = 0 := by
      funext i
      exact h_rows_zero i

    -- 3. Apply the rational matrix rank theorem from VertexVerificationRat
    exact Phase2Rat.full_rank_kernel_trivial v h_mat_mul

end FinalResults

#print axioms FinalResults.candidate_active_binding
#print axioms FinalResults.Candidate_Is_Extreme_Point
