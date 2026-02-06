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
  -- Placeholder: requires an explicit scaling rule for AQEI_functional + bounds.
  -- In many settings, the admissible region is convex but not scale-invariant.
  sorry

theorem cone_closed_under_addition
  (bounds : Bounds L) :
  ∀ T1 T2,
    T1 ∈ AdmissibleCone (L := L) bounds →
    T2 ∈ AdmissibleCone (L := L) bounds →
    (T1 + T2) ∈ AdmissibleCone (L := L) bounds := by
  intro T1 T2 h1 h2
  -- Placeholder: requires compatibility assumptions on the bound term.
  sorry

end ConeProperties
