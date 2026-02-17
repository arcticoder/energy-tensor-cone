import AQEI
import AQEIFamilyInterface

set_option autoImplicit false

/--
  AQEIToInterface.lean

  This is the next "bridge" step:

  - Choose the index type for the AQEI family as `ι := Worldline × SamplingFunction`.
  - Repackage AQEI bounds `bounds : Worldline → SamplingFunction → ℝ` as `b : ι → ℝ`.
  - Assume (for now) that each AQEI functional factors through a continuous linear
    map on a chosen coefficient/topological model `E`.

  With these assumptions, `AQEI.satisfies_AQEI` becomes exactly membership in the
  `AQEIFamily.Admissible` set from `AQEIFamilyInterface.lean`.
-/

namespace AQEIToInterface

open AQEI
open AQEIFamily

section Index

variable {V : Type} [AddCommMonoid V] [Module ℝ V]
variable {L : LorentzSpace V}

/-- The canonical index type for AQEI constraints. -/
abbrev ι (V : Type) [AddCommMonoid V] [Module ℝ V] (L : LorentzSpace V) : Type :=
  Worldline V L × SamplingFunction

/-- Map `(γ,s)` to the index type (just pairing). -/
abbrev idx (γ : Worldline V L) (s : SamplingFunction) : ι (V := V) L := (γ, s)

@[simp] theorem idx_fst (γ : Worldline V L) (s : SamplingFunction) : (idx (V := V) (L := L) γ s).1 = γ := rfl
@[simp] theorem idx_snd (γ : Worldline V L) (s : SamplingFunction) : (idx (V := V) (L := L) γ s).2 = s := rfl

/-- Repackage bounds `bounds γ s` as a function on indices. -/
abbrev bOfBounds (bounds : AQEI.Bounds (V := V) (L := L)) : ι (V := V) L → ℝ :=
  fun i => bounds i.1 i.2

end Index

section CoeffModel

variable {V : Type} [AddCommMonoid V] [Module ℝ V]
variable {L : LorentzSpace V}

variable {E : Type} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

/--
  A chosen coefficient/topological model `E` for stress-energy tensors.

  `encode` is the (possibly non-injective) representation map from the physics-facing
  `StressEnergy` type to the analytic space where we do convex/topology.
-/
variable (encode : StressEnergy V L → E)

/-- The AQEI family as continuous linear maps on `E`, indexed by `(γ,s)`. -/
abbrev functionalCLM : ι (V := V) L → E →L[ℝ] ℝ :=
  fun _ => 0

/--
  Assumption: the physics-facing functional `AQEI_functional (γ,s)` factors through
  the coefficient model via a continuous linear map.

  In practice, this is where one proves that the concrete AQEI integral is linear
  and continuous with respect to the chosen topology on coefficients.
-/
def FactorsThrough
    (Lmap : ι (V := V) L → E →L[ℝ] ℝ) : Prop :=
  ∀ (γ : Worldline V L) (s : SamplingFunction) (T : StressEnergy V L),
    AQEI_functional (V := V) (L := L) (γ := γ) (s := s) T = (Lmap (γ, s)) (encode T)

variable (Lmap : ι (V := V) L → E →L[ℝ] ℝ)

/-- The induced admissible set in coefficient space `E`. -/
abbrev admissibleE (bounds : AQEI.Bounds (V := V) (L := L)) : Set E :=
  Admissible (E := E) (ι := ι (V := V) L) Lmap (bOfBounds (V := V) (L := L) bounds)

/--
  Bridge theorem: if the AQEI functional factors through `E`, then satisfying AQEI
  is equivalent to the encoded point lying in the affine admissible set.

  This is the precise connection needed to apply `AffineToCone` and
  `AQEIFamilyInterface` results to `AQEI.satisfies_AQEI`.
-/
theorem satisfies_AQEI_iff_encode_mem
    (bounds : AQEI.Bounds (V := V) (L := L))
    (hfac : FactorsThrough (V := V) (L := L) encode Lmap) (T : StressEnergy V L) :
    AQEI.satisfies_AQEI (V := V) (L := L) (T := T) bounds ↔ encode T ∈ admissibleE (V := V) (L := L) (E := E) encode Lmap bounds := by
  constructor
  · intro h
    -- Unfold the admissible set and translate the inequality via the factorization.
    intro i
    rcases i with ⟨γ, s⟩
    have hineq : AQEI_functional (V := V) (L := L) (γ := γ) (s := s) T ≥ -bounds γ s := h γ s
    -- Convert to the `0 ≤ ... + ...` form.
    have : 0 ≤ AQEI_functional (V := V) (L := L) (γ := γ) (s := s) T + bounds γ s := by
      linarith
    -- Use factorization.
    simpa [admissibleE, AQEIFamily.Admissible, AffineToCone.AffineAdmissible, bOfBounds, hfac γ s T] using this
  · intro h
    intro γ s
    -- Read off the inequality from membership and undo the `0 ≤` transformation.
    have h0 : 0 ≤ (Lmap (γ, s)) (encode T) + bounds γ s := by
      have := h (γ, s)
      simpa [admissibleE, AQEIFamily.Admissible, AffineToCone.AffineAdmissible, bOfBounds] using this
    -- Replace `(Lmap ...) (encode T)` with `AQEI_functional` via factorization.
    have h1 : 0 ≤ AQEI_functional (V := V) (L := L) (γ := γ) (s := s) T + bounds γ s := by
      simpa [hfac γ s T] using h0
    linarith

end CoeffModel

end AQEIToInterface

-- Completeness checks
#print axioms AQEIToInterface.idx_fst
#print axioms AQEIToInterface.idx_snd
#print axioms AQEIToInterface.satisfies_AQEI_iff_encode_mem

