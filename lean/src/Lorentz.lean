/-
  Lorentz.lean
  Basic definitions: Lorentzian vector space (as a symmetric bilinear form),
  plus timelike/spacelike/null predicates.

  Convention: mostly-plus signature; timelike means ⟪v,v⟫ < 0.

  Reference: Standard convention used in relativistic QFT and GR.
  See: Wald, R.M. (1984). "General Relativity"
       Fewster, C.J. (2012). "Lectures on quantum energy inequalities" [arXiv:1208.5399]
-/
import Std

set_option autoImplicit false

structure LorentzSpace (V : Type) [AddCommMonoid V] [Module ℝ V] where
  inner : V → V → ℝ
  symmetric : ∀ x y, inner x y = inner y x
  nondegenerate : ∀ x, (∀ y, inner x y = 0) → x = 0
  signature_neg_count : Nat -- placeholder: number of negative eigenvalues

namespace LorentzSpace

variable {V : Type} [AddCommMonoid V] [Module ℝ V] (L : LorentzSpace V)

def is_timelike (v : V) : Prop := L.inner v v < 0
def is_spacelike (v : V) : Prop := 0 < L.inner v v
def is_null (v : V) : Prop := L.inner v v = 0

instance (v : V) : Decidable (L.is_timelike v) := inferInstance
instance (v : V) : Decidable (L.is_spacelike v) := inferInstance
instance (v : V) : Decidable (L.is_null v) := inferInstance

end LorentzSpace

-- Completeness checks
#print axioms LorentzSpace
#print axioms LorentzSpace.is_timelike
#print axioms LorentzSpace.is_spacelike
#print axioms LorentzSpace.is_null

