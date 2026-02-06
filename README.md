# warp-cone-aqei

Computational + formalization scaffold for exploring **Averaged Quantum Energy Inequality (AQEI)** constraints as an (approximate) intersection of half-spaces, and for feeding randomized search “near-misses” into a Lean 4 skeleton.

This repo is intentionally minimal:
- **Mathematica** (`mathematica/search.m`) runs a randomized finite-Gaussian-basis search in 1+1 Minkowski and exports results to JSON.
- **Python** (`python/orchestrator.py`, `python/analyze_results.py`) runs the search, parses JSON, and generates `lean/src/GeneratedCandidates.lean`.
- **Lean 4** (`lean/src/*.lean`) contains the definitional skeleton (Lorentzian bilinear form, stress-energy, AQEI family, admissible set / “cone”, extreme rays).

## Quickstart

Run the local test entrypoint:

```bash
./run_tests.sh
```

### Notes

- The Mathematica search defaults to `numTrials=20000`, but tests override with `AQEI_NUM_TRIALS` to keep runs fast.
- The Lean files are a **skeleton**: some theorems are left as `sorry` because the analytic content depends on how you model the sampling family, topology, and bounds.
- Terminology: with a nonzero bound term $B_{\gamma,g}$, the admissible region is typically **convex** but not literally a cone under positive scaling unless extra homogeneity assumptions are imposed. The Lean code keeps the requested names but does not force these assumptions.
