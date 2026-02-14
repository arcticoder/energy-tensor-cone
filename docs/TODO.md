**Project Goal**: Submit a high-quality paper on the convex cone of stress-energy tensors satisfying AQEI, combining Lean formalization, computational searches, and verification against known bounds. Ensure rigor through detailed comparisons, code examples, and mathematical derivations where appropriate.

**Current Status (February 14, 2026)**: Repo at https://github.com/DawsonInstitute/energy-tensor-cone. Latest commits (e.g., `486d99f` integrating literature citations, `6bc8b51` adding methodology section and bound-comparison tests) show expanded lit review (~20 refs), enhanced testing, and TODO cleanups. PRD target PDF: `papers/aqei-cone-formalization-prd.pdf`. 

### Priority Tasks

**2. Enhance Testing Rigor**
- python_tests.sh now includes bound validations (beyond smoke); end-to-end via run_tests.sh improves physics rigor (Lean mech proofs + numerical checks). Add Lean sample for cone convexity:
  ```lean
  theorem cone_convex {V : Type} [AddCommMonoid V] [Module ℝ V] {L : LorentzSpace V}
    (bounds : Worldline V L → SamplingFunction → ℝ) :
    ∀ (T1 T2 : StressEnergy V L) (α β : ℝ), 0 ≤ α → 0 ≤ β → satisfies_AQEI T1 bounds → satisfies_AQEI T2 bounds → satisfies_AQEI (α • T1 + β • T2) bounds := by
    intros T1 T2 α β hα hβ h1 h2 γ s
    unfold satisfies_AQEI
    simp [AQEI_functional]  -- Linearity: I(α T1 + β T2) = α I(T1) + β I(T2)
    linarith [h1 γ s, h2 γ s]
  ```
- Update tex: "Rigorous end-to-end testing, including smoke tests and analytic bound validations via python_tests.sh."
- Commit: "Enhance tests with Lean rigor example"