
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
def candidate_v : Vector6 :=
  fun i =>
    match i.val with
    | 0 => (-201930050 : Rat) / 188548783
    | 1 => 100
    | 2 => 100
    | 3 => (-697114919 : Rat) / 954338471
    | 4 => (271445287 : Rat) / 543764461
    | 5 => 100
    | _ => 0

/--
  The 6 functional constraints defining the local geometry around the vertex.
  Rows 0-2: AQEI constraints (Normal derived from active_L).
  Rows 3-5: Box constraints (Normal derived from unit vectors).

  Note: For indices 3-5 (Box constraints x_j ≤ 100), the inequality is -x_j ≥ -100.
  So the functional L is -e_j, and the bound -B is -100.
  The verification_matrix stores +e_j. So we apply a sign flip for i >= 3.
--/
def L_poly (i : Fin 6) : Vector6 →ₗ[Rat] Rat :=
  let sign : Rat := if i < 3 then 1 else -1
  sign • (LinearMap.proj i).comp (Matrix.mulVecLin Phase2Rat.verification_matrix)

/-- The RHS bounds for the 6 active constraints.
    For AQEI constraints (i < 3): stored as exact rational values equal to -(L_i · v*),
    computed in exact arithmetic from the rationalized L and v* (see active_B_tight in
    AQEI_Generated_Data_Rat.lean). These are NOT derived from candidate_v inside this
    definition, so candidate_active_binding is a non-trivial rational-arithmetic check.
    For box constraints (i ≥ 3): fixed bound of 100. -/
def B_poly (i : Fin 6) : Rat :=
  match i.val with
  | 0 => (36286065376054059506337885986767 : Rat) / 339120078382890596879902371141156
  | 1 => (56881163208213718514020808481935025194233775134029935638377 : Rat) / 532124755520295182874251714890874438355108028311061855673287
  | 2 => (237683910384684634846040317252027915796047109138197689971 : Rat) / 2153503410892270359210740429201985008222235476670837870345
  | _ => 100  -- box bounds: x_j ≤ 100 ↔ -x_j ≥ -100

/- Proof that the candidate point exactly satisfies the equality constraints.
   For i < 3 (AQEI constraints): native_decide evaluates the rational matrix-vector
   product L_poly i candidate_v and checks it equals -B_poly i (a stored literal).
   For i ≥ 3 (box constraints): same tactic verifies x_j = 100. -/
theorem candidate_active_binding : ∀ i : Fin 6, L_poly i candidate_v = -B_poly i := by
  intro i
  fin_cases i <;>
    simp [L_poly, B_poly, LinearMap.smul_apply, LinearMap.comp_apply,
      Matrix.mulVecLin_apply, LinearMap.proj_apply, smul_eq_mul,
      candidate_v, Phase2Rat.verification_matrix,
      Phase2Rat.row0, Phase2Rat.row1, Phase2Rat.row2,
      Phase2Rat.row3, Phase2Rat.row4, Phase2Rat.row5,
      Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_six] <;>
    native_decide

/--
  The Candidate Vertex is an Extreme Point of the polyhedron defined by the 6 active constraints.
-/
theorem Candidate_Is_Extreme_Point :
  ConvexGeometry.IsExtremePoint (k := Rat) (PolyhedralGeometry.Polyhedron L_poly B_poly) candidate_v := by
  refine PolyhedralGeometry.full_rank_active_implies_vertex (k := Rat) (E := Vector6) (ι := Fin 6)
      L_poly B_poly candidate_v Set.univ ?_ ?_ ?_
  · -- Feasibility
    simp [PolyhedralGeometry.Polyhedron]
    intro i
    simp [candidate_active_binding i]
  · -- All constraints are active (by definition of the polyhedron we constructed)
    intro i _
    exact candidate_active_binding i
  · -- Full Rank (Trivial Kernel Condition)
    intro v hv
    -- Goal: v = 0
    -- Hyp: ∀ i, L_poly i v = 0
    have h_mul : ∀ i, (Matrix.mulVec Phase2Rat.verification_matrix v) i = 0 := by
      intro i
      have hv0 := hv i (Set.mem_univ i)
      by_cases hi : i < 3
      · simpa [L_poly, hi, LinearMap.smul_apply, LinearMap.comp_apply,
          Matrix.mulVecLin_apply, LinearMap.proj_apply] using hv0
      · have hneg : -(Matrix.mulVec Phase2Rat.verification_matrix v) i = 0 := by
          simpa [L_poly, hi, LinearMap.smul_apply, LinearMap.comp_apply,
            Matrix.mulVecLin_apply, LinearMap.proj_apply] using hv0
        exact (neg_eq_zero.mp hneg)

    have h_mat_mul : Matrix.mulVec Phase2Rat.verification_matrix v = 0 := by
      funext i
      exact h_mul i

    exact Phase2Rat.full_rank_kernel_trivial v h_mat_mul

end FinalResults

#print axioms FinalResults.candidate_active_binding
#print axioms FinalResults.Candidate_Is_Extreme_Point
#print axioms FinalResults.candidate_v
#print axioms FinalResults.L_poly
#print axioms FinalResults.B_poly
