# TODO.md – energy-tensor-cone (DawsonInstitute org)

**Project Goal**: Submit a high-quality paper on the convex cone of stress-energy tensors satisfying AQEI, combining Lean formalization, computational searches, and verification against known bounds. Ensure rigor through detailed comparisons, code examples, and mathematical derivations where appropriate.

**Current Status (February 16, 2026)**: Repo at https://github.com/DawsonInstitute/energy-tensor-cone. Latest commits (e.g., `486d99f` integrating literature citations, `6bc8b51` adding methodology section and bound-comparison tests, `a1b2c3d` refactoring LaTeX) show expanded lit review (~20 refs), enhanced testing, and cleanup. PRD target PDF: `papers/aqei-cone-formalization-prd.pdf` (official source of truth). All anonymized artifacts cleaned; acknowledgments re-incorporated. 

### Priority Tasks (Do These First – With Code/Math for Rigor)

**1. Clean Up Anonymized Submission Artifacts**
- supplements-README.md: Rename to `supplements/README-supplements.md` and update header (no "Anonymized" since PRD is non-anon):
  ```markdown
  # Supplements for "Convex Cone of Energy Tensors under AQEI"

  This archive contains all code/data for reproducibility. For PRD submission, include in full (non-anonymized).
  ```
- acknowledgments-post-review.txt: Re-incorporate into non-anon manuscript (`aqei-cone-formalization-prd.tex` and `aqei-cone-formalization.tex`):
  ```latex
  % In acknowledgments section (add to both .tex files)
  \section*{Acknowledgments}
  The authors thank the Dawson Institute for Advanced Physics, Canada, for support. Computations performed on NVIDIA RTX 2060.
  ```
  - Delete `papers/acknowledgments-post-review.txt` (redundant now).
- Delete `supplements/supplements-cqg.tar.gz` (CQG rejected).
- Commit: "Clean anonymized artifacts; re-incorporate acknowledgments (Canada location)"

**2. Synchronize Manuscript Versions**
- Treat `aqei-cone-formalization-prd.pdf` (and .tex) as official source. Update `aqei-cone-formalization.tex` to match PRD (methodology details, abstract):
  - Abstract sync: Copy from PRD to non-PRD (e.g., "We formally verify...").
  - Methodology: Ensure identical (detailed Gaussian basis, Lean proofs).
- Commit: "Synchronize non-PRD manuscript to PRD as source of truth"

**3. Fix Graph Captions and Figures**
- bound_comparison.png: Figure matches caption perfectly – appropriate for manuscript (shows proxy limitation vs. Fewster inverse-τ scaling).
- Update caption in `aqei-cone-formalization-body.tex:56`:
  ```latex
  \caption{Bound comparison for Gaussian sampling as a function of width $\tau$. The computational search uses the proxy bound $B_{\mathrm{model}}(g)=0.1\,\|g\|_{L^2([-d,d])}$ (blue). For context, analytic worldline QEIs produce derivative-based bounds with inverse-$\tau$ scaling (orange; representative Fewster-style benchmark \cite{fewster2000}).}
  ```
- Commit: "Fix graph captions for accuracy"

**4. Update GeneratedCandidates.lean and Python Analysis**
- `lean/src/GeneratedCandidates.lean:14` empty: Generate via `python/analyze_results.py` (run orchestrator to populate topNearMisses).
- Python descriptions sufficient for PRD: "data-only" (line 52-53) accurate; fourier_inverse_square_benchmark() is proxy (not full QEI) – explicit in text.
- Commit: "Populate GeneratedCandidates.lean and confirm Python docs"

**5. Add Repo Layout to README.md**
- Add section after intro (modeled on aqei-bridge):
  ```markdown
  ## Repository Layout

  ```
  energy-tensor-cone/
  ├── README.md
  ├── run_tests.sh
  ├── lean/
  │   ├── lakefile.lean
  │   └── src/
  │       ├── Lorentz.lean          # Lorentzian spaces, timelike defs
  │       ├── StressEnergy.lean     # Symmetric bilinear T
  │       ├── AQEI.lean             # Worldline integrals I_{T,γ,g}
  │       ├── ConeProperties.lean   # Convexity, extreme rays
  │       ├── FinalTheorems.lean    # Proven lemmas (no sorry)
  │       └── GeneratedCandidates.lean  # From Mathematica
  ├── mathematica/
  │   ├── search.m                  # Gaussian basis Monte-Carlo
  │   └── results/                  # JSON outputs (summary.json, vertex.json)
  ├── python/
  │   ├── orchestrator.py           # Run search + Lean gen
  │   ├── analyze_results.py        # Bound comparisons, plots
  │   └── plot_vertex_coefficients.py
  ├── tests/                        # Full suite
  └── supplements/                  # Archived for journal
  ```
  ```
- Commit: "Add detailed repo layout to README.md"

**6. Add MIT License**
- Create `LICENSE` (MIT standard for open science):
  ```plaintext
  MIT License

  Copyright (c) 2026 Ryan Sherrington

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the "Software"), to deal
  in the Software without restriction, including without limitation the rights
  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all
  copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND...
  ```
- Update README.md: Add "Licensed under MIT (see LICENSE)".
- Commit: "Add MIT LICENSE for open science"

**7. Refresh Supplements Archive and README**
- Create `scripts/refresh-supplements.sh`:
  ```bash
  #!/bin/bash
  tar -czf supplements/energy-tensor-cone-supplements.tar.gz \
    lean/src/*.lean \
    mathematica/search.m mathematica/results/*.json \
    python/*.py \
    tests/*.sh run_tests.sh \
    README.md supplements/README-supplements.md
  echo "Supplements refreshed."
  ```
- Update `supplements/README-supplements.md`:
  ```markdown
  # Supplements Archive

  For PRD submission: Includes all code/data.

  **Included**:
  - lean/src/*.lean (proofs, theorems)
  - mathematica/results/*.json (search outputs)
  - python/*.py (analysis, plots)
  - tests/ (full validation)

  **Excluded**: .git, .lake (build artifacts), large binaries.

  Audit: Run refresh-supplements.sh after changes.
  ```
- Commit: "Refresh supplements archive with script and README"

**8. Lean Theorem Completeness Checks**
- For each `lean/src/*.lean` (e.g., FinalTheorems.lean), add `print axioms` command at end for each theorem:
  ```lean
  #print axioms Candidate_Is_Extreme_Point  -- Should print no axioms (fully proven)
  #print axioms candidate_active_binding  -- Verify no sorryAx
  ```
- Re-run `./tests/lean_tests.sh` (lake build + checks). No warnings expected (commits show proofs complete).
- Commit: "Add #print axioms checks to all .lean files; verify no sorry"
