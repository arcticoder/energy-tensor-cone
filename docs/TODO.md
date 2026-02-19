# TODO.md – energy-tensor-cone (DawsonInstitute org)

**Project Goal**: Submit a high-quality paper on the convex cone of stress-energy tensors satisfying AQEI, combining Lean formalization, computational searches, and verification against known bounds.

**Current Status (February 19, 2026)**: All PRD submission review items complete. Working through documentation/tooling polish tasks.

See `TODO-completed.md` for the full history of completed tasks.

---

## Active Tasks

### A1. Remove ci.yml; convert to local setup script
Convert `.github/workflows/ci.yml` into a local dependency-check/setup script
(`tests/check_deps.sh`). Remove ci.yml (and `.github/workflows/` directory).
Ensure `README.md` describes how to install deps and run tests locally.

### A2. Update stale docs/verification.md (Feb 6 → Feb 19)
`docs/verification.md` pre-dates the Feb 18 audit. Add a status header noting all
H1–H3/M1–M8/L1–L6 issues were found and resolved. No need to rewrite fully.

### A3. Update stale docs/theorem_verification.md (Feb 6 → Feb 19)
Add status header: theorem count is 35+2 (2 intentional `sorry`), `rows_match_active_L`
added, `Lean.ofReduceBool` axiom documented.

### A4. Update stale docs/test_validation.md (Feb 6 → Feb 19)
Add status header: test suite overhauled (Lean compilation errors were not caught
originally; `verify_vertex.py` now invoked; plot smoke test; CI added then removed).

### A5. Add Fewster (2012) citations in Lean source files
`docs/verification.md:2`: "Add explicit comments in Lean files citing Fewster (2012)
for AQEI." The header of `lean/src/AQEI.lean` has them; confirm individual
`AQEI_functional` definitions also reference the citation.

### A6. Document AQEI_functional placeholder nature more explicitly
`docs/verification.md:3`: "Document the placeholder nature of `AQEI_functional`
in comments." Current docstring says "returns 0"; add explicit note pointing to
`AQEI_functional_toy` and to the Mathematica/Python implementation as the concrete
realization for this paper.

### A7. Link AQEI_functional_toy to free scalar field in comments
`docs/verification.md:4`: "Implement concrete functional for specific QFT (e.g.,
free scalar field)." The `AQEI_functional_toy` discrete Riemann sum is an
approximation; add a comment explaining how this connects to the 1+1D free scalar
field energy density discretized in the Gaussian basis.

### A8. Fix supplements tar: add missing files
`supplements/energy-tensor-cone-supplements.tar.gz` is missing:
`lean/lake-manifest.json`, `lean/lakefile.lean`, `lean/lean-toolchain`,
`lean/test_polyhedral.lean`, `tools/generate_lean_data_rat.py`,
`tools/generate_lean_data.py`, `tools/translate_vertex.py`, `tools/verify_vertex.py`
Update `scripts/refresh-supplements.sh` and regenerate the archive.

### A9. Delete papers/aqei_cone_structure.md (redundant with LaTeX source)
Remove the 51-line Markdown outline; the paper exists in definitive LaTeX form.
The PDF is the rendered artifact.

### A10. Create scripts/refresh-manuscript-source.sh; regenerate manuscript-source.zip
`papers/manuscript-source.zip` is for PRD submission (source upload).
Create a reproducible script that packages all required LaTeX source files:
`.tex`, `.bib`, `.cls`, `figures/`. Update `README.md` to describe the zip.

### A11. README: remove "(Complete)" from layout heading
`README.md` line 19: "Repository Layout (Complete)" → "Repository Layout".

### A12. README: add descriptions to docs/ entries #30-37
`docs/verification.md`, `docs/test_validation.md`, `docs/theorem_verification.md`
are undescribed in the layout table.

### A13. README: add description to supplements/README-supplements.md entry
`README.md` line 27: `supplements/README-supplements.md` has no description.

### A14. README: add lean/test_polyhedral.lean and lean/lean-toolchain to layout
`README.md` lines 38–58 omits these two files.

### A15. README: remove .github/workflows/ entry after ci.yml deleted (A1)
After A1 is complete, remove the `.github/workflows/` block from the layout table.

### A16. README: fix tools/ location (repo root, not python/tools/)
`README.md` lines 71-75 lists `tools/` under `python/`. It is actually at the
repo root. Move the entry and update descriptions.

### A17. README: add missing papers/ files to layout
Missing from layout: `papers/aqei-cone-formalization-prd.pdf`,
`papers/aqei-cone-formalization.pdf`, `papers/aqei_cone_structure.md` (to be
deleted per A9), `papers/common-preamble.tex`, `papers/common-theorems.tex`,
`papers/manuscript-source.zip`.

### A18. README: expand Paper section description (#19)
Mention `aqei-cone-formalization.tex`, `common-preamble.tex`, `common-theorems.tex`,
`iopjournal.cls`, and the `figures/` directory in the Paper section narrative.

### A19. README: clarify N=100 note does not block PRD submission (#8)
`README.md` line 14: add a parenthetical making clear this note is about scope,
not a blocker. Certified vertex is the N=6 result.

---

## Completed ✅

All items from the comprehensive PRD submission review audit (H1-H3, M1-M8, L1-L6, README) were resolved in commits `1f619c8` and `ae7efc8`. See `TODO-completed.md`.

---

## Future Work (Not Required for Submission)

- **M7 (data consistency)**: Add test that re-runs `generate_lean_data_rat.py` and diffs against `AQEI_Generated_Data_Rat.lean` to guard against stale certified data.
- **L2 (Gaussian normalization)**: Add normalization prefactor to basis functions in `search.m` and note physical interpretation implications in paper.
- **3+1D extension**: Generalize from 1+1D Minkowski to 3+1D.
- **Symbolic bounds**: Replace proxy bound $B_{\text{model}}$ with exact analytic Fewster-style bound.
- **Infinite-dimensional theory**: Connect finite polytope certificate to full QFT.
