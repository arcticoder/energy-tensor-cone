**Project Goal**: Submit a high-quality paper on the convex cone of stress-energy tensors satisfying AQEI, combining Lean formalization, computational searches, and verification against known bounds.

**Current Status (February 14, 2026)**: Repo at https://github.com/DawsonInstitute/energy-tensor-cone. Paper revised post-CQG rejection with expanded lit review (now ~20 refs). PRD target PDF: `papers/aqei-cone-formalization-prd.pdf`. Testing and README polishes needed for full readiness.

### Priority Tasks (Do These First)

**1. Assess PRD Readiness and Add Tasks**
- With 20 references, revisions from CQG feedback (expanded overview, more figures/connections), and core proofs: Yes, ready to publish to PRD after minor polishes below. PRD accepts computational/formal QFT work; our lit balance (AQEI core + math/formal) is sufficient (typical PRD papers: 20-50 refs; ours fits focused articles).
- Add tasks: Expand testing to full end-to-end (beyond smoke); add 1-2 more figures (e.g., bound comparisons).
- Commit: "Update README and add PRD-specific tasks for submission readiness"

**2. Check PRD Prep Guidelines (journals.aps.org/prl/authors#prepare-your-manuscript)**
- See ~/Code/asciimath/energy/docs/journals/PRD/prepare-your-manuscript.html
- All key items done: REVTeX used, abstract <600 chars, references in order, no tracked changes. Still needed: Ensure word count fits (PRD no strict limit, but concise); add PACS codes if required (optional but recommended for classification – e.g., 03.70.+k Quantum information, 04.60.-m Quantum gravity).
- Commit: "Add PACS codes and confirm PRD guidelines compliance in tex"

**4. Refactor LaTeX Further**
- Maintain 3 .tex versions via shared inputs (common-preamble.tex, etc.). For revisions, edit shared files; use git branches (e.g., git checkout -b prd-revision) for PRD-specific tweaks.
- Reminder PRD doesn't support anonymized submissions.
- Commit: "Enhance LaTeX refactoring for multi-journal support"

**5. Clarify mathematica/results in Manuscript**
- Update tex (line 97): "...representative JSON outputs (e.g., summary.json, near_misses.json) under mathematica/results/..." – Clearer now post-.gitignore removal; list example files.
- Commit: "Update tex description of results dir"

**6. Address vertex_coefficients.png Concerns**
- No major concerns – binary-like distribution (0/100) fits finite discretization (e.g., active/inactive modes). Ensure caption explains: "Verified coefficients for a candidate vertex, showing binary activation pattern consistent with polyhedral structure."
- If values seem off (negatives near zero), verify script (`python/plot_vertex_coefficients.py`) and regenerate if needed.
- Commit: "Review and update figure caption for vertex coefficients"

**8. Update README.md**
- Line 10: Replace CQG with "PRD (Physical Review D)".
- Line 13: "Minimal" is good – highlights focus; add "with extensible structure for further dimensions/QFT extensions".
- Line 15: Update Python list: Include `plot_vertex_coefficients.py`, `generate_lean_data.py`, etc. (full find output).
- Commit: "Polish README for PRD and completeness"

**9. Enhance Testing for Rigor**
- python_tests.sh smoke-test sufficient for submission (many physics papers rely on similar); but for rigor, expand to full end-to-end: Add scripts validating against analytic bounds (e.g., Fewster scalars).
- Update tex (line 92/190): Clarify "smoke + end-to-end validation via orchestrator.py".
- Note: Not full rigor yet, but publishable – add task for bound-validation tests.
- Commit: "Expand tests to include bound comparisons"

### Final Pre-Submission Checklist (to PRD)
- All polishes done; submit via https://authors.aps.org/Submissions/.
- Update README/sites post-submission.