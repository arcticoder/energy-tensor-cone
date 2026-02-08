# Supplementary Materials

**Paper**: Convex Cone of Energy Tensors under AQEI: Formal Verification and Computational Exploration  
**Authors**: Ryan Sherrington, Dawson Institute for Advanced Physics  
**Date**: February 2026

## Contents

This supplementary archive contains the complete computational and formal verification code for the paper, organized as follows:

### 1. Lean 4 Formal Proofs (`lean/`)

The `lean/` directory contains all Lean 4 source files with formally verified theorems:

- `lakefile.lean` - Lean project configuration
- `src/` - Source files:
  - `Lorentz.lean` - Lorentzian bilinear forms and signatures
  - `StressEnergy.lean` - Stress-energy tensor definitions
  - `AQEI.lean` - AQEI functional definitions
  - `ConeProperties.lean` - Basic cone properties
  - `AQEIFamilyInterface.lean` - Abstract AQEI family interface (main closure/convexity theorems)
  - `AffineToCone.lean` - Homogenization construction
  - `PolyhedralVertex.lean` - Vertex characterization theorems
  - `ExtremeRays.lean` - Extreme ray definitions
  - `VertexVerificationRat.lean` - Rational arithmetic vertex verification
  - `FinalTheorems.lean` - Main results combining all components

**Requirements**:
- Lean 4 (v4.14.0 or later)
- Mathlib4

**Build Instructions**:
```bash
cd lean
lake build
```

### 2. Mathematica Computational Search (`mathematica/`)

The `mathematica/` directory contains the optimization-based search for extreme rays:

- `search.m` - Main search script using linear programming
  - Generates random Gaussian basis in 1+1D Minkowski space
  - Constructs AQEI constraints
  - Searches for boundary configurations
  - Exports results to JSON

**Requirements**:
- Wolfram Mathematica (tested with version 13+) or wolframscript

**Usage**:
```bash
cd mathematica
wolframscript -file search.m
```

**Output**: Results exported to `mathematica/results/` (vertex.json, summary.json, etc.)

### 3. Python Analysis Pipeline (`python/`)

The `python/` directory contains data processing and Lean code generation:

- `orchestrator.py` - Runs full pipeline (Mathematica → Python → Lean)
- `analyze_results.py` - Parses JSON results and generates Lean code

**Requirements**:
- Python 3.8+
- matplotlib, json (stdlib)

**Usage**:
```bash
cd python
python orchestrator.py
```

### 4. Test Suite (`tests/`)

Automated tests for all components:

- `build_lean.sh` - Verifies Lean build
- `python_tests.sh` - Tests Python analysis
- `mathematica_tests.sh` - Tests Mathematica search
- `lean_tests.sh` - Tests Lean proofs

**Run all tests**:
```bash
./run_tests.sh
```

## Reproducibility

To reproduce the results in the paper:

1. Build Lean proofs: `cd lean && lake build`
2. Run Mathematica search: `cd mathematica && wolframscript -file search.m`
3. Process results: `cd python && python orchestrator.py`
4. Run full test suite: `./run_tests.sh`

All tests should pass, confirming:
- Lean theorems verified
- Mathematica finds vertex with 6 active constraints
- Python pipeline generates valid Lean code
- End-to-end integration successful

## Source Code Repository

The complete source code is publicly available at:
https://github.com/DawsonInstitute/energy-tensor-cone

For questions or issues, please open a GitHub issue or contact rsherrington@dawsoninstitute.org.

##License

See LICENSE file in the root directory.
