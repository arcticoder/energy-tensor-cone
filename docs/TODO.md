# TODO.md – energy-tensor-cone (DawsonInstitute org)

**Project Goal**: Submit a high-quality paper on the convex cone of stress-energy tensors satisfying AQEI, combining Lean formalization, computational searches, and verification against known bounds.

**Current Status (February 18, 2026)**: All core tasks complete. `lake build` succeeds with no errors across all 17 Lean files. PRD target PDF: `papers/aqei-cone-formalization-prd.pdf`.

See `TODO-completed.md` for the full history of completed tasks.

### Completed ✅

All priority tasks completed as of February 18, 2026:
- **Lean formalization**: 35 theorems proven, 0 unintentional `sorry`, all 17 files build cleanly via `lake build`
- **Main conjecture**: Closure, convexity, and extreme-ray certificate all mechanically verified in Lean 4
- **Manuscript**: `papers/aqei-cone-formalization-prd.tex` ready for PRD submission
- **Full details**: See `TODO-completed.md`

### Future Work (Not Required for Submission)

- **3+1D extension**: Generalize from 1+1D Minkowski to 3+1D; handle additional stress-energy components
- **Symbolic bounds**: Replace proxy bound $B_{\text{model}}$ with exact analytic Fewster-style bound derived from first principles
- **Infinite-dimensional theory**: Connect finite polytope certificate to abstract cone in infinite-dimensional setting
- **arXiv/journal submission**: Upload to arXiv (math-ph, gr-qc, hep-th); target Communications in Mathematical Physics or PRD
