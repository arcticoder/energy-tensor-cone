Completed: *Run tests, commit, push* (6/6)

**Done**
- Created public repo: https://github.com/arcticoder/warp-cone-aqei
- Cloned to `~/Code/asciimath/energy/warp-cone-aqei`
- Added it to the multi-root workspace: energy/energy.code-workspace

**Repo Layout + Contents**
- Local entrypoint: run_tests.sh
- Mathematica randomized search (exports `top_near_misses.json`): search.m
- Lean skeleton (typechecks via `lake build`):  
  - Lorentz.lean  
  - StressEnergy.lean  
  - AQEI.lean  
  - ConeProperties.lean
- Python glue + Lean candidate generator:  
  - orchestrator.py  
  - analyze_results.py
- Test harness scripts: tests

**Verification**
- run_tests.sh passes end-to-end (Python smoke tests + fast Mathematica run + `lake build`).
- Initial commit pushed to `origin/main`.
<!-- ------ -->
---
**What I pushed**
- Added Mathlib to the Lean project so we can actually prove topology/convexity facts: lakefile.lean
- Added a *proved* finite-dimensional model that matches the “finite AQEI constraints = half-spaces” heuristic and proves:
  - closedness (finite intersection of closed half-spaces),
  - convexity,
  - and a **nontrivial extreme ray** (basis vector in the nonnegative orthant):
  - FiniteToyModel.lean
- Wired it into the library build: WarpConeAqei.lean
- Cleaned up repo hygiene so we don’t track build outputs: .gitignore (and removed previously-tracked .lake, __pycache__, and results artifacts)

**Why this is real progress toward the conjecture**
- The conjecture’s “convex cone” part is immediate once each AQEI constraint is a linear functional inequality; the subtle parts are (a) closedness under an infinite family and a chosen topology and (b) existence/structure of extreme rays.
- This commit makes the **finite-family approximation** fully formal in Lean and demonstrates **explicit extreme rays** in a clean toy cone (nonnegative orthant). That’s the template we can generalize.
<!-- ------ -->
---
**Done**
- Committed and pushed the pending Lean work: added AffineToCone.lean and updated WarpConeAqei.lean to import it.
- `origin/main` now includes commit `009dcf7` (“Homogenize affine AQEI bounds into a cone…”).

**Verified**
- Full repo test harness passes: run_tests.sh ends with “All tests passed.” (Python + Mathematica + Lean).

**Most proof-likely next step (chosen)**
- Prioritize the “closed + convex” part for an *infinite* AQEI family, then use homogenization to restore cone structure.
- Rationale: closedness/convexity for arbitrary families is structurally robust (intersection of closed/convex half-spaces), whereas “nontrivial extreme rays” becomes delicate outside finite-dimensional / polyhedral settings.

**Lean formalization improvement**
- Strengthened `AffineToCone.lean` with general (possibly infinite-index) results:
  - `affineAdmissible_isClosed`
  - `affineAdmissible_convex`
  - generalized `homCone_isClosed` to drop the unnecessary `Fintype` assumption
<!-- ------ -->
---
