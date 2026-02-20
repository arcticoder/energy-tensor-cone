/-
  PolyhedralVertex.lean

  Formal proof that "Full Rank Active Constraints" implies "Extreme Point".
  This connects the computational rank check to the geometric definition of a vertex.
-/
import Mathlib
import ExtremeRays

set_option autoImplicit false

namespace PolyhedralGeometry

section VertexTheorem

variable {k : Type} [LinearOrderedField k]
variable {E : Type} [AddCommGroup E] [Module k E]

/-- A polyhedron defined by a family of linear inequalities L_i(x) ≥ -B_i. -/
def Polyhedron {ι : Type} (L : ι → E →ₗ[k] k) (B : ι → k) : Set E :=
  { x | ∀ i, L i x ≥ -B i }

/--
  The Main Theorem:
  If x satisfies the constraints, and there exists a finite subset of constraints 'active'
  such that L_i(x) = -B_i and the L_i span the dual space (full rank),
  then x is an extreme point of the polyhedron.
-/
theorem full_rank_active_implies_vertex
    {ι : Type}
    (L : ι → E →ₗ[k] k)
    (B : ι → k)
    (x : E)
    (active : Set ι)
    (h_feasible : x ∈ Polyhedron L B)
    (h_active_binding : ∀ i ∈ active, L i x = -B i)
    -- The spanning condition: The only vector orthogonal to all active L_i is 0.
    -- This is equivalent to "L_i span the dual space".
    (h_full_rank : ∀ v : E, (∀ i ∈ active, L i v = 0) → v = 0) :
    ConvexGeometry.IsExtremePoint (k := k) (Polyhedron L B) x := by
  constructor
  · exact h_feasible
  · intros y z t hy hz ht0 ht1 h_convex_comb
    -- Strategy: Show that y and z must also satisfy the active constraints with equality,
    -- then use full rank to conclude y = x and z = x.

    have h_segment_active : ∀ i ∈ active, L i y = -B i ∧ L i z = -B i := by
      intro i hi
      have hy_ge : L i y ≥ -B i := hy i
      have hz_ge : L i z ≥ -B i := hz i
      -- t * L i y + (1-t) * L i z = L i x = -B i
      have h_comb : t * L i y + (1 - t) * L i z = -B i := by
        have := congr_arg (L i) h_convex_comb
        simp [map_add, map_smul] at this
        linarith [h_active_binding i hi]
      -- For reals a,b ≥ c and t*a + (1-t)*b = c with 0 < t < 1: a = c and b = c
      constructor
      · nlinarith [mul_nonneg (le_of_lt ht0) (sub_nonneg.mpr hy_ge),
                   mul_nonneg (sub_nonneg.mpr (le_of_lt ht1)) (sub_nonneg.mpr hz_ge)]
      · nlinarith [mul_nonneg (le_of_lt ht0) (sub_nonneg.mpr hy_ge),
                   mul_nonneg (sub_nonneg.mpr (le_of_lt ht1)) (sub_nonneg.mpr hz_ge)]

    have h_y_eq_x : y = x := by
      have h0 : y - x = 0 := h_full_rank (y - x) (fun i hi => by
        simp [map_sub]
        rw [(h_segment_active i hi).1, h_active_binding i hi]
        ring)
      exact eq_of_sub_eq_zero h0

    have h_z_eq_x : z = x := by
      have h0 : z - x = 0 := h_full_rank (z - x) (fun i hi => by
        simp [map_sub]
        rw [(h_segment_active i hi).2, h_active_binding i hi]
        ring)
      exact eq_of_sub_eq_zero h0

    exact ⟨h_y_eq_x, h_z_eq_x⟩

end VertexTheorem

end PolyhedralGeometry

-- Completeness checks
#print axioms PolyhedralGeometry.full_rank_active_implies_vertex
#print axioms PolyhedralGeometry.Polyhedron

