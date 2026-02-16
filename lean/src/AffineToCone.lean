/-
  AffineToCone.lean

  Why this file exists:

  AQEI constraints in practice often look like

    I(T,γ,g) ≥ -B(γ,g)

  i.e. an affine half-space constraint in T (because of the additive bound B).
  The intersection of affine half-spaces is convex and closed (under mild
  continuity assumptions), but it is *not* necessarily a cone under scaling.

  Standard fix: homogenize.

  If we write constraints as `0 ≤ L i x + b i`, then define a cone in `E × ℝ`:

    Ĉ := { (x,t) | 0 ≤ t ∧ ∀ i, 0 ≤ L i x + t * b i }

  Then:
  - the slice t = 1 recovers the original admissible set,
  - Ĉ is closed and convex (intersection of closed/convex half-spaces),
  - Ĉ is a genuine cone under nonnegative scaling.

  This is the most direct path to a fully formal “closed convex cone” theorem
  compatible with nonzero AQEI bounds.
-/

import Mathlib

set_option autoImplicit false

namespace AffineToCone

open scoped BigOperators

section General

variable {E : Type} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
variable {ι : Type}

/-- Affine (bound-shifted) admissible set: `∀ i, 0 ≤ L i x + b i`. -/
def AffineAdmissible (L : ι → E →L[ℝ] ℝ) (b : ι → ℝ) : Set E :=
  {x | ∀ i : ι, 0 ≤ (L i) x + b i}

/-- Homogenized cone in `E × ℝ`: `t ≥ 0` and `∀ i, 0 ≤ L i x + t*b i`. -/
def HomCone (L : ι → E →L[ℝ] ℝ) (b : ι → ℝ) : Set (E × ℝ) :=
  {p | 0 ≤ p.2 ∧ ∀ i : ι, 0 ≤ (L i) p.1 + p.2 * b i}

/-- Closedness of the affine admissible set (arbitrary intersection of closed half-spaces). -/
theorem affineAdmissible_isClosed (L : ι → E →L[ℝ] ℝ) (b : ι → ℝ) :
    IsClosed (AffineAdmissible (E := E) L b) := by
  classical
  -- `AffineAdmissible` is an intersection over `i` of `{x | 0 ≤ L i x + b i}`.
  have hi : ∀ i : ι, IsClosed {x : E | 0 ≤ (L i) x + b i} := by
    intro i
    have hcont : Continuous fun x : E => (L i) x + b i := (L i).continuous.add continuous_const
    simpa using (isClosed_Ici.preimage hcont)
  -- Assemble the intersection.
  have : AffineAdmissible (E := E) L b = ⋂ i : ι, {x : E | 0 ≤ (L i) x + b i} := by
    ext x
    simp [AffineAdmissible]
  simpa [this] using isClosed_iInter hi

/-- Convexity of the affine admissible set (intersection of convex half-spaces). -/
theorem affineAdmissible_convex (L : ι → E →L[ℝ] ℝ) (b : ι → ℝ) :
    Convex ℝ (AffineAdmissible (E := E) L b) := by
  classical
  -- Each constraint set `{x | 0 ≤ L i x + b i}` is convex.
  have hi : ∀ i : ι, Convex ℝ {x : E | 0 ≤ (L i) x + b i} := by
    intro i
    intro x hx y hy a c ha hc hac
    -- Use the affine-linear identity with `a+c=1`.
    --
    -- L(a•x+c•y) + b = a*(Lx+b) + c*(Ly+b)
    have : 0 ≤ a * ((L i) x + b i) + c * ((L i) y + b i) :=
      add_nonneg (mul_nonneg ha hx) (mul_nonneg hc hy)
    -- Rewrite the target using linearity and `hac : a + c = 1`.
    --
    -- `b = (a+c)*b` so we can distribute it across the convex combination.
    simpa [map_add, map_smul, smul_eq_mul, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, hac,
      add_assoc, add_left_comm, add_comm] using this
  -- Intersection of convex sets is convex.
  have : AffineAdmissible (E := E) L b = ⋂ i : ι, {x : E | 0 ≤ (L i) x + b i} := by
    ext x
    simp [AffineAdmissible]
  simpa [this] using convex_iInter hi

@[simp]
theorem mem_homCone {L : ι → E →L[ℝ] ℝ} {b : ι → ℝ} {p : E × ℝ} :
    p ∈ HomCone (E := E) L b ↔ (0 ≤ p.2 ∧ ∀ i : ι, 0 ≤ (L i) p.1 + p.2 * b i) := by
  rfl

/-- Slice relation: `x` satisfies the affine constraints iff `(x,1)` is in the homogenized cone. -/
theorem slice_one_iff (L : ι → E →L[ℝ] ℝ) (b : ι → ℝ) (x : E) :
    x ∈ AffineAdmissible (E := E) L b ↔ (x, (1 : ℝ)) ∈ HomCone (E := E) L b := by
  constructor
  · intro hx
    refine ⟨by norm_num, ?_⟩
    intro i
    simpa [AffineAdmissible] using hx i
  · intro hx
    intro i
    have := (hx.2 i)
    simpa [AffineAdmissible] using this

/-- Closedness of the homogenized cone, assuming a `Fintype` index so we can use finite intersections.

For the real AQEI family, the index is infinite; closedness is still true as an arbitrary intersection
of closed sets, but this finite version is the cleanest starting point and avoids extra topology
boilerplate.
-/
theorem homCone_isClosed
  (L : ι → E →L[ℝ] ℝ) (b : ι → ℝ) :
    IsClosed (HomCone (E := E) L b) := by
  classical
  -- Represent as intersection of two kinds of closed constraints.
  -- 1) `0 ≤ t`
  -- 2) For each i, `0 ≤ L i x + t*b i`
  have h0 : IsClosed {p : E × ℝ | 0 ≤ p.2} := by
    -- preimage of `Ici 0` under continuous `Prod.snd`
    simpa [Set.preimage, Set.Ici] using (isClosed_Ici.preimage (continuous_snd : Continuous fun p : E × ℝ => p.2))

  have hi : ∀ i : ι, IsClosed {p : E × ℝ | 0 ≤ (L i) p.1 + p.2 * b i} := by
    intro i
    -- continuous map p ↦ L i (fst p) + (snd p) * b i
    have hcont1 : Continuous fun p : E × ℝ => (L i) p.1 := (L i).continuous.comp continuous_fst
    have hcont2 : Continuous fun p : E × ℝ => p.2 * b i := (continuous_snd.mul continuous_const)
    have hcont : Continuous fun p : E × ℝ => (L i) p.1 + p.2 * b i := hcont1.add hcont2
    -- preimage of `Ici 0`
    simpa using (isClosed_Ici.preimage hcont)

  -- Now assemble.
  have : HomCone (E := E) L b = ({p : E × ℝ | 0 ≤ p.2} ∩ ⋂ i : ι, {p : E × ℝ | 0 ≤ (L i) p.1 + p.2 * b i}) := by
    ext p
    simp [HomCone, Set.mem_iInter, and_left_comm, and_assoc, and_comm]

  -- Arbitrary intersection.
  simpa [this] using h0.inter (isClosed_iInter (fun i : ι => hi i))

/-- Convexity of the homogenized cone (finite family; convexity also holds for infinite intersections). -/
theorem homCone_convex
    (L : ι → E →L[ℝ] ℝ) (b : ι → ℝ) :
    Convex ℝ (HomCone (E := E) L b) := by
  intro p hp q hq a c ha hc hac
  refine ⟨?_, ?_⟩
  · -- t coordinate
    have : 0 ≤ a * p.2 + c * q.2 :=
      add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hc hq.1)
    simpa [Prod.snd_add, Prod.snd_smul, Pi.add_apply, smul_eq_mul, hac, add_comm, add_left_comm, add_assoc] using this
  · intro i
    -- Use linearity of L and distributivity.
    -- Define shorthand for the constraint expression.
    have hp_i := hp.2 i
    have hq_i := hq.2 i
    -- Expand target:
    -- 0 ≤ L i (a•p.1 + c•q.1) + (a*p.2 + c*q.2) * b i
    --    = a*(L i p.1 + p.2*b i) + c*(L i q.1 + q.2*b i)
    -- then apply nonneg combination.
    have : 0 ≤ a * ((L i) p.1 + p.2 * b i) + c * ((L i) q.1 + q.2 * b i) :=
      add_nonneg (mul_nonneg ha hp_i) (mul_nonneg hc hq_i)

    -- Rewrite the LHS to the goal form.
    -- Use simp to push scalar multiplication through linear map and through Prod.
    -- Note: `smul_eq_mul` since scalar field is ℝ.
    -- Also, in Prod, scalar action is componentwise.
    --
    -- We'll do it in a single `simpa` step.
    simpa [HomCone, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm,
      map_add, map_smul, hac, Prod.fst_add, Prod.fst_smul, Prod.snd_add, Prod.snd_smul, add_assoc, add_left_comm,
      add_comm] using this

/-- Cone property: closed under scaling by a nonnegative scalar. -/
theorem homCone_smul_nonneg
    (L : ι → E →L[ℝ] ℝ) (b : ι → ℝ) :
    ∀ (p : E × ℝ) (α : ℝ), p ∈ HomCone (E := E) L b → 0 ≤ α → (α • p) ∈ HomCone (E := E) L b := by
  intro p α hp hα
  refine ⟨?_, ?_⟩
  · -- t coordinate scales
    simpa [Prod.snd_smul, smul_eq_mul, mul_nonneg] using (mul_nonneg hα hp.1)
  · intro i
    -- Constraint scales linearly.
    -- (L i) (α•x) + (α*t)*b = α*((L i) x + t*b)
    have : 0 ≤ α * ((L i) p.1 + p.2 * b i) := mul_nonneg hα (hp.2 i)
    simpa [Prod.fst_smul, Prod.snd_smul, smul_eq_mul, map_smul, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using this

end General

section ExtremeRayExample

/-- Simple extreme-ray witness in the homogenized cone for the orthant.

This proves “nontrivial extreme rays” in a cone that directly matches the
half-space intersection pattern.
-/

abbrev E (n : Nat) := Fin n → ℝ

def OrthantCone (n : Nat) : Set (E n × ℝ) :=
  {p | 0 ≤ p.2 ∧ ∀ i, 0 ≤ p.1 i}

/-- Standard basis vector in `ℝ^n`. -/
def basisVec {n : Nat} (i : Fin n) : E n := fun j => if j = i then 1 else 0

/-- A minimal “extreme ray” predicate. -/
def IsExtremeRay {X : Type} [AddCommMonoid X] [Module ℝ X] (C : Set X) (r : X) : Prop :=
  r ≠ 0 ∧ r ∈ C ∧
    ∀ x y,
      x ∈ C → y ∈ C → r = x + y →
        (∃ (λ : ℝ), 0 ≤ λ ∧ x = λ • r) ∧ (∃ (μ : ℝ), 0 ≤ μ ∧ y = μ • r)

/-- Extreme ray along a coordinate axis at `t=0`: `(e_i, 0)` is an extreme ray of the cone `x ≥ 0, t ≥ 0`. -/
theorem orthant_basis_extreme {n : Nat} (i : Fin n) :
    IsExtremeRay (OrthantCone n) (basisVec (n := n) i, (0 : ℝ)) := by
  -- Adapt the argument from `FiniteToyModel.basisVec_isExtremeRay`.
  refine ⟨?_, ?_, ?_⟩
  · -- nonzero
    intro h
    have := congrArg (fun p => p.1 i) h
    -- (basisVec i) i = 1, so contradiction.
    simpa [basisVec] using this
  · -- membership
    refine ⟨by simp, ?_⟩
    intro j
    by_cases hji : j = i
    · subst hji; simp [basisVec]
    · simp [basisVec, hji]
  · intro x y hx hy hxy
    -- Off-axis coordinates must be 0 in both x and y.
    have hx0 : ∀ j : Fin n, j ≠ i → x.1 j = 0 := by
      intro j hj
      have hsum : x.1 j + y.1 j = (basisVec (n := n) i) j := by
        have : (x + y).1 j = (basisVec (n := n) i, (0 : ℝ)).1 j := by simpa [hxy]
        simpa [Prod.fst_add, Pi.add_apply] using this
      have hb : (basisVec (n := n) i) j = 0 := by simp [basisVec, hj]
      have hsum0 : x.1 j + y.1 j = 0 := by simpa [hb] using hsum
      have xle0 : x.1 j ≤ 0 := by
        calc
          x.1 j ≤ x.1 j + y.1 j := le_add_of_nonneg_right (hy.2 j)
          _ = 0 := hsum0
      exact le_antisymm xle0 (hx.2 j)

    have hy0 : ∀ j : Fin n, j ≠ i → y.1 j = 0 := by
      intro j hj
      have hsum : x.1 j + y.1 j = (basisVec (n := n) i) j := by
        have : (x + y).1 j = (basisVec (n := n) i, (0 : ℝ)).1 j := by simpa [hxy]
        simpa [Prod.fst_add, Pi.add_apply] using this
      have hb : (basisVec (n := n) i) j = 0 := by simp [basisVec, hj]
      have hsum0 : x.1 j + y.1 j = 0 := by simpa [hb] using hsum
      have yle0 : y.1 j ≤ 0 := by
        calc
          y.1 j ≤ x.1 j + y.1 j := le_add_of_nonneg_left (hx.2 j)
          _ = 0 := hsum0
      exact le_antisymm yle0 (hy.2 j)

    -- Also t-components: 0 = x.2 + y.2, with both ≥ 0, hence x.2 = 0 and y.2 = 0.
    have xt0 : x.2 = 0 := by
      have : (basisVec (n := n) i, (0 : ℝ)).2 = (x + y).2 := by simpa [hxy]
      have hsum0 : x.2 + y.2 = 0 := by simpa [Prod.snd_add] using this.symm
      have xle0 : x.2 ≤ 0 := by
        calc
          x.2 ≤ x.2 + y.2 := le_add_of_nonneg_right hy.1
          _ = 0 := hsum0
      exact le_antisymm xle0 hx.1

    have yt0 : y.2 = 0 := by
      have : (basisVec (n := n) i, (0 : ℝ)).2 = (x + y).2 := by simpa [hxy]
      have hsum0 : x.2 + y.2 = 0 := by simpa [Prod.snd_add] using this.symm
      have yle0 : y.2 ≤ 0 := by
        calc
          y.2 ≤ x.2 + y.2 := le_add_of_nonneg_left hx.1
          _ = 0 := hsum0
      exact le_antisymm yle0 hy.1

    -- λ = x_i, μ = y_i
    refine ⟨⟨x.1 i, hx.2 i, ?_⟩, ⟨y.1 i, hy.2 i, ?_⟩⟩
    · ext1
      · -- first component function ext
        ext j
        by_cases hj : j = i
        · subst hj
          simp [basisVec, Pi.smul_apply]
        · have : x.1 j = 0 := hx0 j hj
          simp [basisVec, hj, this, Pi.smul_apply]
      · -- second component
        simp [xt0]
    · ext1
      · ext j
        by_cases hj : j = i
        · subst hj
          simp [basisVec, Pi.smul_apply]
        · have : y.1 j = 0 := hy0 j hj
          simp [basisVec, hj, this, Pi.smul_apply]
      · simp [yt0]

end ExtremeRayExample

end AffineToCone

-- Completeness checks
#print axioms affineAdmissible_isClosed
#print axioms affineAdmissible_convex
#print axioms mem_homCone
#print axioms slice_one_iff
#print axioms homCone_isClosed
#print axioms homCone_convex
#print axioms homCone_smul_nonneg
#print axioms orthant_basis_extreme

