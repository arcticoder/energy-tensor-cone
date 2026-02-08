# TODO.md – energy-tensor-cone

**Project Goal**: Submit a high-quality paper on the convex cone of stress-energy tensors satisfying AQEI, with Lean formalization + computational evidence.

**Current Status (as of February 7, 2026)**: Tasks 1-5 completed. Paper compiles cleanly. Remaining tasks: supplements, edits, git fixes, GitHub metadata.

### Remaining Tasks

**6. Prepare Journal Submission Supplements Zip (This Week)**
- Include: Full repo zip (or key dirs: lean/src/*.lean, mathematica/search.m, python/*.py, tests/*), generated results (e.g., mathematica/results/*), and a README-supplements.md explaining usage.
- Exclude binaries/PDFs; refer to GitHub for full repo.
- Commit: "Prepare supplements zip"

**7. Additional Edits to aqei-cone-formalization.tex (This Week)**
- Add "Verification and Limitations" section after results: Discuss 1+1D model limits, comparison to analytic bounds, future work on full QFT.
- Improve abstract: Make concise, highlight novelty (Lean + computation for AQEI cone/first formal verification of AQEI cone properties).
- Add figures if possible (e.g., near-miss plots from Python, analyze_results.py plots).
- Ensure all \cite are proper; remove inline arXiv mentions.
- Proofread for typos/math consistency.
- check overfull hboxes (e.g., line 92-93: shorten text).
- Commit: "Edits to LaTeX for polish and completeness"

**8. Additional Citations to Add (Ongoing)**
- fewster2008 already in bib (downloaded arxiv version to papers/related/fewster2008.tex)
- Ensure all keys match bib.
- Update as needed.

**9. Git log fixes**
Fix commit author and email so they're all from Arcticoder <10162808+arcticoder@users.noreply.github.com>.
Use git filter-branch or git rebase to fix commit history.

**10. Github repo details**
Update the github repo (DawsonInstitute/energy-tensor-cone) "About" and set Topics for the repo using the `gh` command and/or github api.

### Final Pre-Submission Checklist
- Compile clean PDF.
- Upload to arXiv (categories: math-ph primary, gr-qc/hep-th cross).
- Submit to CMP
