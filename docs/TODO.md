# TODO.md – energy-tensor-cone (DawsonInstitute org)

**Project Goal**: Submit a high-quality paper on the convex cone of stress-energy tensors satisfying AQEI, combining Lean formalization, computational searches, and verification against known bounds.

**Current Status (February 8, 2026)**: Repo at https://github.com/DawsonInstitute/energy-tensor-cone. Paper at restricted Zenodo (https://zenodo.org/records/18522457), anonymized repo at https://anonymous.4open.science/r/aqei-convex-cone-5789/. CQG submission started; double-anonymous selected. Address form fields below.

### Priority Tasks (Do These First)

**1. Create Anonymized Manuscript and Supplements for Double-Anonymous CQG Review (Today)**
- Anonymize `papers/aqei-cone-formalization.tex`: Remove author name, affiliation, email, acknowledgments (move to separate file for post-review). Use placeholders like "Anonymous Authors" if needed. Replace GitHub links with anonymized repo: https://anonymous.4open.science/r/aqei-convex-cone-5789/. Ensure no identifying info (e.g., remove Zenodo link or make it generic).
- Anonymized supplements: Create `papers/supplements-anon.zip` with redacted files (lean/src without personal comments, mathematica/search.m, python/*.py, tests/* – no names/emails). Reference anonymized repo in data statement.
- Anonymity assessment: Per IOP checklist (https://publishingsupport.iopscience.iop.org/questions/checklist-for-anonymising-your-manuscript/), you've made a good faith effort (restricted Zenodo, anonymized repo). **Do not include the GitHub link in the submission manuscript** to avoid risks – instead, say "Code available in anonymized repository upon request during review." Keep the main repo public (no need to private it) as anonymity focuses on the submission file. This meets CQG's double-anonymous standards.
- Commit: "Create anonymized tex and supplements for CQG double-anonymous review" (do not push identifying changes to public repo).

**2. Additional Verification & Polish Tasks (This Week)**
- **Dimensionality (1+1D)**: No extension to 3+1 needed – publishable as is. Many AQEI papers start low-dim; your contribution is the formal/computational framework. Note in limitations: "Future work: Extend to 3+1D for full spacetime relevance."
- **Infinite-dim QFT connection**: No – finite basis is the innovation; discuss approximations in paper. Not burdening others; it's incremental science.
- **Comparisons with analytic bounds**: Yes – add subsection in "Verification and Limitations": Numerically compare your Gaussian-basis results (near-misses) to Fewster's scalar field bounds (e.g., from 2012 review). Run simulations if needed; cite explicitly.

### Final Pre-Submission Checklist
- Anonymized PDF/supplements ready.
- Submit to CQG.
- After submission, update README/sites with CQG status.