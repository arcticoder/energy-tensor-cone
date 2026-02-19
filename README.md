# energy-tensor-cone

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18522457.svg)](https://doi.org/10.5281/zenodo.18522457)

Computational + formalization scaffold for exploring **Averaged Quantum Energy Inequality (AQEI)** constraints as an (approximate) intersection of half-spaces, and for feeding randomized search "near-misses" into a Lean 4 skeleton.

**Status**: 
- **Published at Zenodo**: [DOI 10.5281/zenodo.18522457](https://doi.org/10.5281/zenodo.18522457)
- **Organization**: [DawsonInstitute/energy-tensor-cone](https://github.com/DawsonInstitute/energy-tensor-cone)
- **Manuscript (PRD / Physical Review D target)**: REV\TeX wrapper at `papers/aqei-cone-formalization-prd.tex` with shared body `papers/aqei-cone-formalization-body.tex` (build artifact: `papers/aqei-cone-formalization-prd.pdf`)
- **arXiv submission**: Planned (math-ph primary; secondary gr-qc, hep-th)

This repo is intentionally minimal:
- **Mathematica** (`mathematica/search.m`) runs a randomized finite-Gaussian-basis LP search (default: $N=6$ basis elements, $M=50$ constraints) in 1+1 Minkowski and exports `vertex.json`. All four parameters (`AQEI_NUM_BASIS`, `AQEI_NUM_CONSTRAINTS`, `AQEI_DOMAIN`, `AQEI_SIGMA`) plus the random seed (`AQEI_SEED`, default 42) are overridable via environment variables. *Note: Scaling experiments with $N=100$/$M=500$ are supported but produce uncertified vertices — this is a scope note, not a publication blocker; the certified vertex is the N=6 result.*
- **Python** (`python/__init__.py`, `python/orchestrator.py`, `python/analyze_results.py`, `python/plot_vertex_coefficients.py`, `python/plot_bound_comparison.py`) runs the search, parses JSON, generates `lean/src/GeneratedCandidates.lean`, and produces the manuscript figures.
- **Tools** (`tools/generate_lean_data.py`, `tools/generate_lean_data_rat.py`, `tools/translate_vertex.py`, `tools/verify_vertex.py`) provide data translation and independent numerical checks for the exported vertex/certificate artifacts.
- **Lean 4** (`lean/src/*.lean`) contains the definitional skeleton (Lorentzian bilinear form, stress-energy, AQEI family, admissible set / "cone", extreme rays).

## Repository Layout

```
energy-tensor-cone/
├── README.md                          # Overview, replication
├── LICENSE                            # MIT
├── run_tests.sh                       # Full pipeline (Lean + Python + Mathematica)
├── supplements/                       # Journal archive
│   ├── energy-tensor-cone-supplements.tar.gz  # Source archive for journal submission
│   └── README-supplements.md          # What is/isn't included in the archive
├── docs/                              # Internal tracking
│   ├── TODO.md                        # Active tasks
│   ├── TODO-completed.md              # Completed task log
│   ├── TODO-BLOCKED.md                # Blocked items awaiting external input
│   ├── history/
│   │   └── history.md                 # Session-by-session change log
│   ├── verification.md                # Mathematical definition cross-checks vs. literature
│   ├── test_validation.md             # Test suite validation report
│   └── theorem_verification.md        # Lean theorem inventory (35 proven + 2 intentional sorry)
├── lean/                              # Formal core
│   ├── lakefile.lean                  # Lake build config (Lean 4 project)
│   ├── lake-manifest.json             # Pinned dependency versions
│   ├── lean-toolchain                 # Lean 4 toolchain version pin (v4.14.0)
│   ├── test_polyhedral.lean           # Standalone polyhedral geometry check
│   └── src/
│       ├── Lorentz.lean               # LorentzSpace, is_timelike
│       ├── StressEnergy.lean          # T bilinear, energy_density
│       ├── AQEI.lean                  # I_{T,γ,g} functionals
│       ├── ConeProperties.lean        # Convexity, extreme rays (intentional sorry for false theorems)
│       ├── FinalTheorems.lean         # Main theorems (Candidate_Is_Extreme_Point)
│       ├── GeneratedCandidates.lean   # Data from Mathematica (Float, for visualization)
│       ├── AQEI_Generated_Data.lean   # Float data structure
│       ├── AQEI_Generated_Data_Rat.lean # Rational data (active_L, active_B, active_B_tight)
│       ├── AQEIFamilyInterface.lean   # Abstract interface: closure, convexity
│       ├── AQEIToInterface.lean       # Bridge to physics definitions
│       ├── AffineToCone.lean          # Homogenization theorems
│       ├── ExtremeRays.lean           # Extreme point definitions
│       ├── FiniteToyModel.lean        # Finite-dimensional examples
│       ├── PolyhedralVertex.lean      # Polyhedral vertex theorems
│       ├── VertexVerification.lean    # Float-based checks
│       ├── VertexVerificationRat.lean # Rational verification (det ≠ 0, row consistency)
│       └── WarpConeAqei.lean          # Module imports
├── mathematica/                       # Search engine
│   ├── search.m                       # LP solver (default N=6, M=50, seed=42)
│   └── results/                       # JSON outputs
│       └── vertex.json                # Certified vertex (active constraints + coefficients)
├── python/                            # Glue + analysis
│   ├── __init__.py
│   ├── orchestrator.py                # Orchestrate Mathematica search → Python analysis → Lean gen
│   ├── analyze_results.py             # Parse vertex.json, compute bounds, call plotting
│   ├── plot_vertex_coefficients.py    # Generate figures/vertex_coefficients.png
│   └── plot_bound_comparison.py       # Generate figures/bound_comparison.png
├── tools/                             # Data translation and independent verification
│   ├── generate_lean_data.py          # Convert vertex.json floats → GeneratedCandidates.lean
│   ├── generate_lean_data_rat.py      # Convert to rational literals → AQEI_Generated_Data_Rat.lean
│   ├── translate_vertex.py            # Vertex data format conversion utilities
│   └── verify_vertex.py              # Independent scipy re-integration of active constraints (called by tests)
├── tests/                             # Test suite
│   ├── check_deps.sh                  # Verify required tools/packages are installed
│   ├── build_lean.sh                  # lake build only
│   ├── python_tests.sh                # Smoke tests + bound validation + plot test
│   ├── mathematica_tests.sh           # Search execution (skipped if wolframscript absent)
│   └── lean_tests.sh                  # Lean build + sorry/axiom checks
├── papers/                            # Manuscript files
│   ├── aqei-cone-formalization-body.tex      # Shared manuscript body (Introduction → Appendix)
│   ├── aqei-cone-formalization.tex           # Article.cls wrapper (for arXiv/preprint)
│   ├── aqei-cone-formalization-prd.tex       # REVTeX 4.2 wrapper (Physical Review D target)
│   ├── aqei-cone-formalization.bib           # BibTeX bibliography
│   ├── common-preamble.tex                   # Shared LaTeX preamble (packages, macros)
│   ├── common-theorems.tex                   # Shared theorem environments
│   ├── iopjournal.cls                         # IOP journal class (for alternative submission)
│   ├── manuscript-source.zip                 # Packaged source for PRD online submission
│   ├── aqei-cone-formalization-prd.pdf       # PRD compiled PDF (build artifact)
│   ├── aqei-cone-formalization.pdf           # Article.cls compiled PDF (build artifact)
│   └── figures/
│       ├── bound_comparison.png              # Proxy bound vs. Fewster scaling (Figure 1)
│       └── vertex_coefficients.png           # Certified vertex coefficients (Figure 2)
└── scripts/
    ├── refresh-supplements.sh         # Regenerate supplements/energy-tensor-cone-supplements.tar.gz
    └── refresh-manuscript-source.sh   # Regenerate papers/manuscript-source.zip for PRD submission
```

## Paper

The manuscript body is in `papers/aqei-cone-formalization-body.tex`, shared by two wrappers:
- **`papers/aqei-cone-formalization-prd.tex`** — REVTeX 4.2 wrapper for Physical Review D submission (compiled PDF: `papers/aqei-cone-formalization-prd.pdf`)
- **`papers/aqei-cone-formalization.tex`** — Article.cls wrapper for arXiv preprint (compiled PDF: `papers/aqei-cone-formalization.pdf`)

Supporting LaTeX files: `common-preamble.tex` (packages/macros), `common-theorems.tex` (theorem environments), `iopjournal.cls` (IOP class, kept for reference), `papers/aqei-cone-formalization.bib` (bibliography). Figures are in `papers/figures/`.

`papers/manuscript-source.zip` is the source bundle for PRD online submission. Regenerate it with `bash scripts/refresh-manuscript-source.sh`.

This paper is prepared for submission to:
- **arXiv**: Primary category math-ph (Mathematical Physics), secondary categories gr-qc (General Relativity and Quantum Cosmology) and hep-th (High Energy Physics - Theory)
- **Journal**: Physical Review D (PRD)

## Quickstart

First verify your environment has all required tools:

```bash
bash tests/check_deps.sh
```

Then run the full test suite:

```bash
./run_tests.sh
```

This runs:
- **Lean build verification**: Compiles all formal proofs (`lake build`)
- **Python tests**: Validates data processing pipeline
- **Mathematica tests**: Runs computational search (fast test mode, skipped if wolframscript absent)

### Replication Instructions

To reproduce the full computational + formal verification pipeline:

```bash
# From repository root
cd python
python -m pip install -e .  # Install as module (fixes ModuleNotFoundError)
python orchestrator.py      # Full search + analysis pipeline
cd ..
./run_tests.sh              # Verify all components
```

Alternatively, run individual steps:

1. **Build Lean proofs**: `cd lean && lake build `
2. **Run Mathematica search**: `cd mathematica && wolframscript -file search.m`
3. **Process results**: `cd python && python orchestrator.py`
4. **Run full test suite**: `./run_tests.sh`

See the Reproducibility appendix in the manuscript for complete details.

### Notes on Formal Verification

- **Core theorems proven**: 35 theorems proven across the Lean codebase, including closure/convexity results (AQEIFamilyInterface.lean), homogenization theorems (AffineToCone.lean), vertex characterization (PolyhedralVertex.lean, VertexVerificationRat.lean), and the main certificate theorem (FinalTheorems.Candidate_Is_Extreme_Point). No unintentional `sorry` placeholders in proven results.
- **Intentional `sorry` statements**: Two theorems in `ConeProperties.lean` have `sorry` placeholders because they are intentionally false as stated (AQEI constraints are affine, not homogeneous). These document why bare AQEI regions are not true cones; the correct cone formulation is proven in `AffineToCone.lean`.
- **Axiom basis**: Core proofs depend on `propext`, `Classical.choice`, `Quot.sound` (standard Lean/Mathlib axioms). The `native_decide` tactic used in `VertexVerificationRat.lean` and `FinalTheorems.lean` additionally depends on `Lean.ofReduceBool`, a trusted kernel extension that compiles Lean terms to native code using GMP arbitrary-precision arithmetic for exact rational evaluation.
- **Publication status**: The Lean development provides mechanized proofs of core properties (convexity, extreme-ray candidates in finite models); some extensions remain as `sorry` placeholders for future work. This level of formalization is standard for computational mathematics papers in physics journals — core claims are mechanically verified, while extensions are documented as open questions.

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

## License

Licensed under MIT (see LICENSE).
