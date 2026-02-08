# energy-tensor-cone

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18522457.svg)](https://doi.org/10.5281/zenodo.18522457)

Computational + formalization scaffold for exploring **Averaged Quantum Energy Inequality (AQEI)** constraints as an (approximate) intersection of half-spaces, and for feeding randomized search "near-misses" into a Lean 4 skeleton.

**Status**: 
- **Published at Zenodo**: [DOI 10.5281/zenodo.18522457](https://doi.org/10.5281/zenodo.18522457)
- **Manuscript**: `aqei-cone-formalization.tex` ready for journal submission
- **arXiv submission**: Planned for math-ph (Mathematical Physics), with secondary categories gr-qc, hep-th

This repo is intentionally minimal:
- **Mathematica** (`mathematica/search.m`) runs a randomized finite-Gaussian-basis search in 1+1 Minkowski and exports results to JSON.
- **Python** (`python/orchestrator.py`, `python/analyze_results.py`) runs the search, parses JSON, and generates `lean/src/GeneratedCandidates.lean`.
- **Lean 4** (`lean/src/*.lean`) contains the definitional skeleton (Lorentzian bilinear form, stress-energy, AQEI family, admissible set / "cone", extreme rays).

## Paper

The manuscript is available in `papers/aqei-cone-formalization.tex` and is ready for submission to:
- **arXiv**: Primary category math-ph (Mathematical Physics), secondary categories gr-qc (General Relativity and Quantum Cosmology) and hep-th (High Energy Physics - Theory)
- **Journal**: Communications in Mathematical Physics (CMP)

## Quickstart

Run the local test entrypoint to verify all components:

```bash
./run_tests.sh
```

This runs:
- **Lean build verification**: Compiles all formal proofs (`lake build`)
- **Python tests**: Validates data processing pipeline
- **Mathematica tests**: Runs computational search (fast test mode)

### Replication Instructions

To reproduce the full computational + formal verification pipeline:

1. **Build Lean proofs**: `cd lean && lake build`
2. **Run Mathematica search**: `cd mathematica && wolframscript -file search.m`
3. **Process results**: `cd python && python orchestrator.py`
4. **Run full test suite**: `./run_tests.sh`

See `papers/aqei-cone-formalization.tex` Appendix B for complete details.

### Notes on Formal Verification

- **Core theorems proven**: All 10 critical theorems (closure, convexity, homogenization, vertex characterization) are fully proven in Lean with no placeholders.
- **Intentional `sorry` statements**: Two theorems in `ConeProperties.lean` have `sorry` placeholders because they are intentionally false as stated (AQEI constraints are affine, not homogeneous). These document why bare AQEI regions are not true cones; the correct cone formulation is proven in `AffineToCone.lean`.
- **Publication status**: This level of formalization is standard for computational mathematics papers - core claims are mechanically verified, while extensions remain as documented future work.
- **Test validation**: See `docs/theorem_verification.md` for complete proof inventory.

### Notes on Terminology

- The Mathematica search defaults to `numTrials=20000`, but tests override with `AQEI_NUM_TRIALS` to keep runs fast.
- With a nonzero bound term $B_{\gamma,g}$, the admissible region is typically **convex** but not literally a cone under positive scaling unless extra homogeneity assumptions are imposed. The homogenized cone construction (proven in `AffineToCone.lean`) resolves this by embedding the affine constraints in a higher-dimensional space.
