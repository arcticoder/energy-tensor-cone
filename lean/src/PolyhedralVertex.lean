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
def Polyhedron {ι : Type} (L : ι → E →L[k] k) (B : ι → k) : Set E :=
  { x | ∀ i, L i x ≥ -B i }

/--
  The Main Theorem:
  If x satisfies the constraints, and there exists a finite subset of constraints 'active'
  such that L_i(x) = -B_i and the L_i span the dual space (full rank),
  then x is an extreme point of the polyhedron.
-/
theorem full_rank_active_implies_vertex
    {ι : Type}
    (L : ι → E →L[k] k)
    (B : ι → k)
    (x : E)
    (active : Set ι)
    (h_feasible : x ∈ Polyhedron L B)
    (h_active_binding : ∀ i ∈ active, L i x = -B i)
    -- The spanning condition: The only vector orthogonal to all active L_i is 0.
    -- This is equivalent to "L_i span the dual space".
    (h_full_rank : ∀ v : E, (∀ i ∈ active, L i v = 0) → v = 0) :
    ConvexGeometry.IsExtremePoint (Polyhedron L B) x := by
  constructor
  · exact h_feasible
  · intros y z t hy hz ht0 ht1 h_convex_comb
    -- We want to prove y = x and z = x.
    -- Strategy: Show that y and z must also satisfy the active constraints with equality.

    have h_segment_active : ∀ i ∈ active, L i y = -B i ∧ L i z = -B i := by
      intro i hi
      -- We know L i y ≥ -B i and L i z ≥ -B i from feasibility
      have hy_ge : L i y ≥ -B i := hy i
      have hz_ge : L i z ≥ -B i := hz i

      -- We know t * L i y + (1-t) * L i z = L i x = -B i
      have h_comb : t * L i y + (1 - t) * L i z = -B i := by
        rw [← map_smul, ← map_smul, ← map_add, h_convex_comb, h_active_binding i hi]

      -- A strictly convex combination of numbers >= K is equal to K
      -- iff both numbers are equal to K.
      exact Convex.combo_eq_bound_impl_eq hy_ge hz_ge ht0 ht1 h_comb

    -- Now consider the difference vector v = y - x.
    -- We want to show v = 0.
    -- Since z = (x - t*y)/(1-t), if y=x then z=x.

    have h_y_eq_x : y = x := by
      apply h_full_rank (y - x)
      intro i hi
      simp
      -- L i (y - x) = L i y - L i x = -B i - (-B i) = 0
      rw [(h_segment_active i hi).1, h_active_binding i hi]
      sub_self _

    have h_z_eq_x : z = x := by
      apply h_full_rank (z - x)
      intro i hi
      simp
      rw [(h_segment_active i hi).2, h_active_binding i hi]
      sub_self _

    exact ⟨h_y_eq_x, h_z_eq_x⟩

end VertexTheorem

end PolyhedralGeometry

-- Completeness checks
#print axioms PolyhedralGeometry.full_rank_active_implies_vertex

