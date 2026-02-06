/-
  AQEI.lean

  We abstract AQEI constraints as an infinite family of inequalities indexed by
  worldlines γ and sampling functions g.

  This file focuses on definitions (skeleton) rather than analytic QFT details.
-/
import Std
import StressEnergy

set_option autoImplicit false

structure SamplingFunction where
  g : ℝ → ℝ
  support_compact : Prop -- placeholder
  nonneg : Prop -- placeholder

structure Worldline (V : Type) [AddCommMonoid V] [Module ℝ V] (L : LorentzSpace V) where
  γ : ℝ → V
  u : ℝ → V
  unit : Prop -- placeholder for normalization

namespace AQEI

open StressEnergy

variable {V : Type} [AddCommMonoid V] [Module ℝ V] {L : LorentzSpace V}

abbrev Bounds := Worldline V L → SamplingFunction → ℝ

/-- Abstract AQEI functional I_{T,γ,g}. In concrete finite models, replace with an integral. -/
def AQEI_functional (γ : Worldline V L) (s : SamplingFunction) : StressEnergy V L → ℝ :=
  fun _T => 0

/-- T satisfies the AQEI family if ∀γ,g: I(T,γ,g) ≥ -B(γ,g). -/
def satisfies_AQEI (T : StressEnergy V L) (bounds : Bounds) : Prop :=
  ∀ (γ : Worldline V L) (s : SamplingFunction), AQEI_functional (γ := γ) (s := s) T ≥ -bounds γ s

end AQEI
