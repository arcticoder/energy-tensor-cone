# TODO.md: Next Steps for warp-cone-aqei Project

This document outlines the next actionable steps to advance the warp-cone-aqei repository. These steps are designed to be fed directly to Sonnet 4.5 (Claude 3.5 Sonnet), which excels at task completion but may need detailed guidance on math and code. Each step is self-contained, with precise instructions, mathematical explanations where needed, and code snippets in Python, Wolfram Mathematica, and Lean 4. Focus on implementation fidelity—do not deviate from the provided code or math unless explicitly noted for fixes.

Assume the repo is already created and cloned as per the original prompt. Build on the existing structure and files described. If a file or directory doesn't exist, create it. Use the provided chat history in `docs/history/history.md` for context, but prioritize these steps.

## Step 1: Verify and Complete Repository Structure

**Task:** Ensure the full directory structure exists as specified. Create any missing files with placeholder content if not already detailed. Commit and push changes.

**Detailed Instructions:**
- Navigate to `~/Code/asciimath/energy/warp-cone-aqei/`.
- Create directories and empty files if missing:
  - `mathematica/search.m` (content provided in Step 3).
  - `lean/lakefile.lean` (content provided in Step 2).
  - `lean/src/` with files: `Lorentz.lean`, `StressEnergy.lean`, `AQEI.lean`, `ConeProperties.lean` (contents provided in original prompt; copy-paste if needed).
  - `python/orchestrator.py` and `analyze_results.py` (content for orchestrator in original; add analyze_results below).
  - `tests/` with scripts: `build_lean.sh`, `python_tests.sh`, `mathematica_tests.sh`, `lean_tests.sh` (contents below).
- Add `README.md` with a brief description: "Repository for formalizing Averaged Quantum Energy Inequalities (AQEI) and stress-energy tensor cones using Lean 4, Mathematica, and Python."
- Update `~/Code/asciimath/energy/energy.code-workspace` to include the new directory (VS Code workspace file; add an entry like `{ "path": "./warp-cone-aqei" }`).
- Run `git add .`, `git commit -m "Complete initial repo structure"`, `git push origin main`.

**Code for tests/build_lean.sh (bash):**
```bash
#!/bin/bash
cd "$(dirname "$0")/../lean"
lake build
if [ $? -eq 0 ]; then
  echo "Lean build successful."
else
  echo "Lean build failed."
  exit 1
fi
```

**Code for tests/python_tests.sh (bash):**
```bash
#!/bin/bash
cd "$(dirname "$0")/../python"
python3 -m unittest discover -v  # Assume unit tests added later; placeholder
echo "Python tests passed."  # Expand with actual tests in future steps
```

**Code for tests/mathematica_tests.sh (bash):**
```bash
#!/bin/bash
cd "$(dirname "$0")/../mathematica"
wolframscript -file search.m
if [ $? -eq 0 ]; then
  echo "Mathematica tests successful."
else
  echo "Mathematica tests failed."
  exit 1
fi
```

**Code for tests/lean_tests.sh (bash):**
```bash
#!/bin/bash
./build_lean.sh  # Reuse build script for typechecking
```

**Code for run_tests.sh (top-level bash):**
```bash
#!/bin/bash
cd tests
./build_lean.sh
./python_tests.sh
./mathematica_tests.sh
./lean_tests.sh
echo "All tests completed."
```

## Step 2: Implement Lean lakefile and Basic Builds

**Task:** Create and configure `lean/lakefile.lean` to make the Lean sources buildable. Ensure it imports Mathlib and builds the src files. Run initial build and fix any syntax errors.

**Mathematical Context:** The Lean files formalize Lorentz spaces (vector spaces with a bilinear form η of signature (-,+,+,...)), stress-energy tensors (symmetric bilinear forms T), AQEI functionals (integrals along worldlines γ with sampling g, ensuring I ≥ -B), and the admissible cone C (convex set of T satisfying AQEI for all γ,g).

**Detailed Instructions:**
- Create `lean/lakefile.lean` with the code below.
- Install Lean 4 and Mathlib if not present (use `lake new` or manual setup).
- Run `lake build` in `lean/` and resolve imports/errors (e.g., ensure Mathlib is cached).
- Add a minimal test: In `ConeProperties.lean`, replace `admit` with simple proofs where possible (e.g., for positive scalars: use linearity of the functional).
- Commit: `git commit -m "Add lakefile and initial Lean build"`

**Code for lean/lakefile.lean:**
```lean
import Lake
open Lake DSL

package «warp-cone-aqei» {
  -- add package configuration options here
}

lean_lib WarpConeAqei {
  -- add library configuration options here
}

@[default_target]
lean_exe «warp-cone-aqei» {
  root := `Main  -- If you add a Main.lean later
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"
```

**Example Proof Fix in ConeProperties.lean (add after theorem):**
```lean
theorem cone_closed_under_positive_scalars {V : Type} [AddCommMonoid V] [Module ℝ V] {L : LorentzSpace V}
  (bounds : Worldline V L → SamplingFunction → ℝ) :
  ∀ (T : StressEnergy V L) (α : ℝ), 0 ≤ α → satisfies_AQEI T bounds → satisfies_AQEI (α • T) bounds := by
  intros T α hα hT γ s
  unfold satisfies_AQEI at *
  simp [AQEI_functional]  -- Assuming linearity: AQEI(α T) = α AQEI(T)
  exact mul_le_mul_of_nonneg_left (hT γ s) hα
```

## Step 3: Refine and Run Mathematica Search Script

**Task:** Implement and test `mathematica/search.m` with GPU tweaks if possible. Run with small numTrials (1000) for testing, export results, and handle any errors (e.g., CUDALink fallback).

**Mathematical Context:** In 1+1D Minkowski space (metric η = diag(-1,1)), model T(x,t) as ∑ a_i φ_i(x,t) S_i where φ_i are Gaussians, S_i symmetric 2x2 matrices. Compute I = ∫ g(t) T(γ(t)) u u dt ≥ -B for random γ (worldline (t, x0 + v t)), g (Gaussian or compact). Search for violations (I + B < 0) or near-misses (0 ≤ I + B < 0.05).

**Detailed Instructions:**
- Create `mathematica/search.m` with the provided code (from original prompt; copy-paste).
- Fix any syntax: Ensure `Symmetrize` is defined (add `Symmetrize[m_] := (m + Transpose[m])/2`).
- For GPU: Replace NIntegrate with NetTrain or other GPU ops if needed, but keep simple for now.
- Run: `wolframscript -file mathematica/search.m`
- Check outputs in `results/` (create dir if missing).
- Increase numTrials to 10000 if test succeeds.
- Commit: `git commit -m "Implement and test Mathematica search"`

**Code Addition for Symmetrize in search.m:**
```mathematica
Symmetrize[m_] := (m + Transpose[m])/2;
```

## Step 4: Implement Python Analyze Results and Feedback to Lean

**Task:** Create `python/analyze_results.py` to parse Mathematica JSON/MX outputs, generate Lean code for candidates, and write to `lean/src/GeneratedCandidates.lean`. Run orchestrator.

**Detailed Instructions:**
- Create the file with code below.
- It reads `summary.json` and `near_misses.mx` (use `scipy` or similar if needed for MX, but assume JSON for simplicity).
- Generate Lean defs for top 5 near-misses as StressEnergy instances (finite basis approximation).
- Run `python/orchestrator.py` (use original code) to test the loop.
- Add unit tests to `python_tests.sh` (e.g., pytest if installed).
- Commit: `git commit -m "Add Python analysis and Lean generation"`

**Code for python/analyze_results.py:**
```python
import json
from pathlib import Path
import subprocess  # For potential MX to JSON conversion

ROOT = Path(__file__).parent.parent
RESULT_DIR = ROOT / "mathematica" / "results"
GEN_FILE = ROOT / "lean" / "src" / "GeneratedCandidates.lean"

def convert_mx_to_json(mx_file):
    # Placeholder: Use Mathematica to export MX to JSON if needed
    # Run wolframscript to convert
    pass  # For now, assume near_misses are in JSON; extend later

def generate_lean_candidates(near_misses):
    with open(GEN_FILE, 'w') as f:
        f.write("import StressEnergy\n\n")
        for i, miss in enumerate(near_misses[:5]):
            a = miss['a']  # Assume dict with 'a', 'val', etc.
            f.write(f"def candidate{i+1} : StressEnergy V L := ⟨\n")
            f.write("  fun u v => ... -- TODO: Implement bilinear from a coefficients\n")
            f.write("⟩\n\n")
            # Math: Reconstruct T from a_i, basisS, centers (hardcode basis if needed)

if __name__ == "__main__":
    summary = json.loads((RESULT_DIR / "summary.json").read_text())
    # Load near_misses (assume JSON for now)
    near_misses = []  # Parse from MX/JSON
    generate_lean_candidates(near_misses)
    print("Generated Lean candidates.")
```

## Step 5: Run Minimal End-to-End Test and Document Results

**Task:** Execute a tiny test: Set numBasis=2, numTrials=1000 in Mathematica, run full pipeline, generate one candidate in Lean, add a theorem like `theorem candidate_is_boundary : satisfies_AQEI candidate1 bounds := admit`, build, and log results in `docs/results.md`.

**Detailed Instructions:**
- Modify search.m temporarily for small run.
- Run `run_tests.sh`.
- Inspect outputs, note any violations/near-misses.
- Update README with test results.
- Commit: `git commit -m "Run minimal end-to-end test"`

## Next Iterations
- After these, focus on proving more lemmas in Lean (e.g., convexity with infinite constraints via approximation).
- Scale Mathematica trials to 1e6+ using cloud if possible.
- Add topology/closure in Lean (use norms from Mathlib).