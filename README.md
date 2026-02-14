# energy-tensor-cone

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18522457.svg)](https://doi.org/10.5281/zenodo.18522457)

Computational + formalization scaffold for exploring **Averaged Quantum Energy Inequality (AQEI)** constraints as an (approximate) intersection of half-spaces, and for feeding randomized search "near-misses" into a Lean 4 skeleton.

**Status**: 
- **Published at Zenodo**: [DOI 10.5281/zenodo.18522457](https://doi.org/10.5281/zenodo.18522457)
- **Organization**: Moved to [DawsonInstitute/energy-tensor-cone](https://github.com/DawsonInstitute/energy-tensor-cone)
- **Manuscript (PRD / Physical Review D target)**: REV\TeX wrapper at `papers/aqei-cone-formalization-prd.tex` with shared body `papers/aqei-cone-formalization-body.tex` (build artifact: `papers/aqei-cone-formalization-prd.pdf`)
- **arXiv submission**: Planned (math-ph primary; secondary gr-qc, hep-th)

This repo is intentionally minimal:
- **Mathematica** (`mathematica/search.m`) runs a randomized finite-Gaussian-basis search in 1+1 Minkowski and exports results to JSON.
- **Python** (`python/__init__.py`, `python/orchestrator.py`, `python/analyze_results.py`, `python/plot_vertex_coefficients.py`, `python/plot_bound_comparison.py`) runs the search, parses JSON, generates `lean/src/GeneratedCandidates.lean`, and produces the manuscript figures.
- **Tools** (`tools/generate_lean_data.py`, `tools/generate_lean_data_rat.py`, `tools/translate_vertex.py`, `tools/verify_vertex.py`) provide data translation and independent numerical checks for the exported vertex/certificate artifacts.
- **Lean 4** (`lean/src/*.lean`) contains the definitional skeleton (Lorentzian bilinear form, stress-energy, AQEI family, admissible set / "cone", extreme rays).

## Paper

The PRD/REV\TeX manuscript is available at `papers/aqei-cone-formalization-prd.tex` (wrapper) with shared content in `papers/aqei-cone-formalization-body.tex`.

This paper is prepared for submission to:
- **arXiv**: Primary category math-ph (Mathematical Physics), secondary categories gr-qc (General Relativity and Quantum Cosmology) and hep-th (High Energy Physics - Theory)
- **Journal**: Physical Review D (PRD)

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

See the \emph{Reproducibility} appendix in the manuscript for complete details.

### Notes on Formal Verification

- **Core theorems proven**: All 10 critical theorems (closure, convexity, homogenization, vertex characterization) are fully proven in Lean with no placeholders.
- **Intentional `sorry` statements**: Two theorems in `ConeProperties.lean` have `sorry` placeholders because they are intentionally false as stated (AQEI constraints are affine, not homogeneous). These document why bare AQEI regions are not true cones; the correct cone formulation is proven in `AffineToCone.lean`.
- **Publication status**: The Lean development provides mechanized proofs of core properties (convexity, extreme-ray candidates in finite models); some extensions remain as `sorry` placeholders for future work. This level of formalization is standard for computational mathematics papers in physics journals — core claims are mechanically verified, while extensions are documented as open questions.
- **Test validation**: See `docs/theorem_verification.md` for complete proof inventory.

#### Lean convexity snippet

The cone convexity result is proved in `lean/src/AQEIFamilyInterface.lean` (excerpted below):

```lean
theorem cone_convex (L : Family E ι) (b : Bounds ι) :
		Convex ℝ (AdmissibleCone (E := E) (ι := ι) L b) :=
	homCone_convex (E := E) (ι := ι) L b
```

### Notes on Terminology

- The Mathematica search defaults to `numTrials=20000`, but tests override with `AQEI_NUM_TRIALS` to keep runs fast.
- With a nonzero bound term $B_{\gamma,g}$, the admissible region is typically **convex** but not literally a cone under positive scaling unless extra homogeneity assumptions are imposed. The homogenized cone construction (proven in `AffineToCone.lean`) resolves this by embedding the affine constraints in a higher-dimensional space.
