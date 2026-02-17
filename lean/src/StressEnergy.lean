/-
  StressEnergy.lean
  Stress-energy tensors as symmetric bilinear forms on a LorentzSpace.

  Reference: Standard definition in relativistic field theory.
  See: Hawking, S.W. & Ellis, G.F.R. (1973). "The Large Scale Structure of Space-Time"
       Wald, R.M. (1984). "General Relativity"
-/
import Mathlib
import Lorentz

set_option autoImplicit false

structure StressEnergy (V : Type) [AddCommMonoid V] [Module ℝ V] (L : LorentzSpace V) where
  T : V → V → ℝ
  symmetric : ∀ x y, T x y = T y x

namespace StressEnergy

variable {V : Type} [AddCommMonoid V] [Module ℝ V] {L : LorentzSpace V}

def energy_density (T : StressEnergy V L) (u : V) : ℝ := T.T u u

instance : Zero (StressEnergy V L) where
  zero := { T := fun _ _ => 0, symmetric := by intro x y; simp }

instance : Add (StressEnergy V L) where
  add A B :=
    { T := fun x y => A.T x y + B.T x y
      symmetric := by
        intro x y
        simp [A.symmetric x y, B.symmetric x y, add_comm, add_left_comm, add_assoc] }

instance : SMul ℝ (StressEnergy V L) where
  smul a A :=
    { T := fun x y => a * A.T x y
      symmetric := by intro x y; simp [A.symmetric x y, mul_comm] }

end StressEnergy

-- Completeness checks
#print axioms StressEnergy
#print axioms StressEnergy.energy_density

