# TODO.md – energy-tensor-cone (DawsonInstitute org)

**Project Goal**: Submit a high-quality paper on the convex cone of stress-energy tensors satisfying AQEI, combining Lean formalization, computational searches, and verification against known bounds.

**Current Status (February 19, 2026)**: All PRD submission review items complete. Working through documentation/tooling polish tasks.

See `TODO-completed.md` for the full history of completed tasks.

---

## Active Tasks

No active tasks. Tasks B1–B6 were completed on February 19, 2026 in commit `f3658d8`.
See `TODO-completed.md`.


---

## Completed ✅

- PRD submission review audit (H1–H3, M1–M8, L1–L6, README) — commits `1f619c8`, `ae7efc8`
- Documentation/tooling polish A1–A19 — commits `b08286f`, `db9b16f`

See `TODO-completed.md` for full details.

---

## Future Work (Not Required for Submission)

- **M7 (data consistency)**: Add test that re-runs `generate_lean_data_rat.py` and diffs against `AQEI_Generated_Data_Rat.lean` to guard against stale certified data.
- **L2 (Gaussian normalization)**: Add normalization prefactor to basis functions in `search.m` and note physical interpretation implications in paper.
- **3+1D extension**: Generalize from 1+1D Minkowski to 3+1D.
- **Symbolic bounds**: Replace proxy bound $B_{\text{model}}$ with exact analytic Fewster-style bound.
- **Infinite-dimensional theory**: Connect finite polytope certificate to full QFT.
