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
