import Mathlib

set_option autoImplicit false

/-
  ExtremeRays.lean

  Definitions needed to state the project's "extreme ray" claims precisely.

  Scope:
  - Works for general real vector spaces.
  - Provides a polyhedral "vertex from active constraints" entry point for the
    finite-dimensional approximation.

  Note:
  This file intentionally avoids committing to the physical AQEI topology; it is
  purely convex-geometric.
-/

namespace ConvexGeometry

section ExtremePoint

variable {k : Type} [LinearOrderedField k]
variable {E : Type} [AddCommMonoid E] [Module k E]

/-- `x` is an extreme point of a set `S` if it cannot be written as a nontrivial
convex combination of two distinct points of `S`. -/
def IsExtremePoint (S : Set E) (x : E) : Prop :=
  x ∈ S ∧
    ∀ ⦃y z : E⦄ ⦃t : k⦄,
      y ∈ S → z ∈ S → 0 < t → t < 1 →
      (t • y + (1 - t) • z = x) →
      y = x ∧ z = x

end ExtremePoint

section ExtremeRay

variable {k : Type} [LinearOrderedField k]
variable {E : Type} [AddCommMonoid E] [Module k E]

/-- A subset `C` is a cone if it is closed under scaling by nonnegative scalars. -/
def IsCone (C : Set E) : Prop := ∀ ⦃x : E⦄ ⦃a : k⦄, x ∈ C → 0 ≤ a → a • x ∈ C

/-- `r` generates an extreme ray of the cone `C` if `r ∈ C`, `r ≠ 0`, and whenever
`r = x + y` with `x,y ∈ C`, then `x` and `y` lie on the same ray as `r`.

This is one common definition; other equivalent formulations exist.
-/
def IsExtremeRay (C : Set E) (r : E) : Prop :=
  r ∈ C ∧ r ≠ 0 ∧
    ∀ ⦃x y : E⦄,
      x ∈ C → y ∈ C → x + y = r →
      ∃ (a b : k), 0 ≤ a ∧ 0 ≤ b ∧ x = a • r ∧ y = b • r


end ExtremeRay

end ConvexGeometry

-- Completeness checks
#print axioms ConvexGeometry.IsExtremePoint
#print axioms ConvexGeometry.IsCone
#print axioms ConvexGeometry.IsExtremeRay

