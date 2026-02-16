/-
  ConeProperties.lean

  Define the admissible region of stress-energy tensors under AQEI constraints.

  Note: With a nonzero bound B_{γ,g}, the admissible region is typically convex
  but not a cone under arbitrary positive scaling unless additional homogeneity
  assumptions are imposed. We keep the requested naming and leave key lemmas as
  placeholders.
-/
import Std
import AQEI
import GeneratedCandidates

set_option autoImplicit false

open StressEnergy

namespace ConeProperties

variable {V : Type} [AddCommMonoid V] [Module ℝ V] (L : LorentzSpace V)

abbrev Bounds := AQEI.Bounds (V := V) (L := L)

def AdmissibleCone (bounds : Bounds L) : Set (StressEnergy V L) :=
  { T | AQEI.satisfies_AQEI (T := T) bounds }

/-- Extreme ray definition (for the cone-like structure). -/
def IsExtremeRay (bounds : Bounds L) (r : StressEnergy V L) : Prop :=
  r ≠ 0 ∧ r ∈ AdmissibleCone (L := L) bounds ∧
    ∀ T1 T2,
      T1 ∈ AdmissibleCone (L := L) bounds →
      T2 ∈ AdmissibleCone (L := L) bounds →
      r = T1 + T2 →
      (∃ (λ : ℝ), 0 ≤ λ ∧ T1 = λ • r) ∧ (∃ (μ : ℝ), 0 ≤ μ ∧ T2 = μ • r)

theorem cone_closed_under_positive_scalars
  (bounds : Bounds L) :
  ∀ (T : StressEnergy V L) (α : ℝ), 0 ≤ α →
    T ∈ AdmissibleCone (L := L) bounds → (α • T) ∈ AdmissibleCone (L := L) bounds := by
  intro T α hα hT
  -- NOTE: This property does NOT hold in general for AQEI!
  -- The issue: AQEI constraint is I(T) ≥ -B, which is AFFINE not homogeneous.
  -- Scaling: I(α·T) = α·I(T), but the bound -B does not scale.
  -- So α·T satisfies α·I(T) ≥ -B, which is weaker than I(α·T) ≥ -B when α > 1.
  --
  -- This is why the admissible set is CONVEX but not a CONE.
  -- For homogenization, see AffineToCone.lean which embeds into one higher dimension.
  --
  -- This sorry is INTENTIONAL - the theorem is FALSE as stated.
  -- Kept for historical reference and to document the non-cone nature of AQEI.
  sorry

theorem cone_closed_under_addition
  (bounds : Bounds L) :
  ∀ T1 T2,
    T1 ∈ AdmissibleCone (L := L) bounds →
    T2 ∈ AdmissibleCone (L := L) bounds →
    (T1 + T2) ∈ AdmissibleCone (L := L) bounds := by
  intro T1 T2 h1 h2
  -- NOTE: This property also does NOT hold in general for AQEI!
  -- The issue is similar: If I(T1) ≥ -B and I(T2) ≥ -B, then
  -- I(T1 + T2) = I(T1) + I(T2) ≥ -2B, which is NOT ≥ -B in general.
  --
  -- For CONVEX combinations (α·T1 + (1-α)·T2) the property DOES hold
  -- because α·I(T1) + (1-α)·I(T2) ≥ -α·B - (1-α)·B = -B.
  --
  -- See AQEIFamilyInterface.lean for the correct convexity theorem.
  --
  -- This sorry is INTENTIONAL - the theorem is FALSE as stated.
  -- Kept for historical reference and to document why "cone" naming is imprecise.
  sorry

end ConeProperties

-- Completeness checks
#print axioms ConeProperties.cone_closed_under_positive_scalars
#print axioms ConeProperties.cone_closed_under_addition

