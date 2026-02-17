import AffineToCone

set_option autoImplicit false

/--
  AQEIFamilyInterface.lean

  Bridge layer between the physics-facing AQEI story and the math-facing
  convexity/topology theorems.

  We model a family of AQEI constraints abstractly as:

    L : ι → E →L[ℝ] ℝ      (continuous linear functionals)
    b : ι → ℝ              (additive bounds)

  and impose the inequalities

    0 ≤ L i x + b i

  This is the minimal interface needed to apply the general results in
  `AffineToCone.lean`:

  - the admissible set is closed and convex (even for infinite families),
  - homogenization produces a genuine closed convex cone in `E × ℝ`,
  - the slice `t = 1` recovers the original affine admissible set.
-/

namespace AQEIFamily

open AffineToCone

section General

variable {E : Type} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
variable {ι : Type}

/-- Continuous-linear AQEI family `ι → (E →L[ℝ] ℝ)`. -/
abbrev Family (E : Type) [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] (ι : Type) :=
  ι → E →L[ℝ] ℝ

/-- Additive bounds for each inequality. -/
abbrev Bounds (ι : Type) := ι → ℝ

/-- The affine admissible set for a family `L` with bounds `b`. -/
abbrev Admissible (L : Family E ι) (b : Bounds ι) : Set E :=
  AffineAdmissible (E := E) L b

/-- Homogenized cone associated to `(L,b)` living in `E × ℝ`. -/
abbrev AdmissibleCone (L : Family E ι) (b : Bounds ι) : Set (E × ℝ) :=
  HomCone (E := E) L b

theorem admissible_isClosed (L : Family E ι) (b : Bounds ι) :
    IsClosed (Admissible (E := E) (ι := ι) L b) :=
  affineAdmissible_isClosed (E := E) (ι := ι) L b

theorem admissible_convex (L : Family E ι) (b : Bounds ι) :
    Convex ℝ (Admissible (E := E) (ι := ι) L b) :=
  affineAdmissible_convex (E := E) (ι := ι) L b

theorem cone_isClosed (L : Family E ι) (b : Bounds ι) :
    IsClosed (AdmissibleCone (E := E) (ι := ι) L b) :=
  homCone_isClosed (E := E) (ι := ι) L b

theorem cone_convex (L : Family E ι) (b : Bounds ι) :
    Convex ℝ (AdmissibleCone (E := E) (ι := ι) L b) :=
  homCone_convex (E := E) (ι := ι) L b

theorem cone_smul_nonneg (L : Family E ι) (b : Bounds ι) :
    ∀ (p : E × ℝ) (α : ℝ), p ∈ AdmissibleCone (E := E) (ι := ι) L b → 0 ≤ α →
      (α • p) ∈ AdmissibleCone (E := E) (ι := ι) L b :=
  homCone_smul_nonneg (E := E) (ι := ι) L b

theorem slice_one_iff' (L : Family E ι) (b : Bounds ι) (x : E) :
    x ∈ Admissible (E := E) (ι := ι) L b ↔ (x, (1 : ℝ)) ∈ AdmissibleCone (E := E) (ι := ι) L b :=
  slice_one_iff (E := E) (ι := ι) L b x

end General

section CoefficientModel

/-- A finite-dimensional coefficient model: `ℝ^n` as functions `Fin n → ℝ`.

This mirrors the Mathematica search, where a stress-energy object is represented
by a small vector of coefficients in a chosen basis.
-/
abbrev Coeff (n : Nat) := Fin n → ℝ

variable {n : Nat}

variable {ι : Type}
variable (L : Family (Coeff n) ι) (b : Bounds ι)

-- In this model, all the theorems above apply immediately.
theorem coeff_admissible_isClosed :
    IsClosed (Admissible (E := Coeff n) (ι := ι) L b) :=
  admissible_isClosed (E := Coeff n) (ι := ι) L b

theorem coeff_admissible_convex :
    Convex ℝ (Admissible (E := Coeff n) (ι := ι) L b) :=
  admissible_convex (E := Coeff n) (ι := ι) L b

theorem coeff_cone_isClosed :
    IsClosed (AdmissibleCone (E := Coeff n) (ι := ι) L b) :=
  cone_isClosed (E := Coeff n) (ι := ι) L b

theorem coeff_cone_convex :
    Convex ℝ (AdmissibleCone (E := Coeff n) (ι := ι) L b) :=
  cone_convex (E := Coeff n) (ι := ι) L b

end CoefficientModel

end AQEIFamily

-- Completeness checks
#print axioms AQEIFamily.admissible_isClosed
#print axioms AQEIFamily.admissible_convex
#print axioms AQEIFamily.cone_isClosed
#print axioms AQEIFamily.cone_convex
#print axioms AQEIFamily.cone_smul_nonneg
#print axioms AQEIFamily.slice_one_iff'
#print axioms AQEIFamily.coeff_admissible_isClosed
#print axioms AQEIFamily.coeff_admissible_convex
#print axioms AQEIFamily.coeff_cone_isClosed
#print axioms AQEIFamily.coeff_cone_convex

