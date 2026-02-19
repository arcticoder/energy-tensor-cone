#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

cd "$ROOT_DIR"

python -m py_compile \
  "$ROOT_DIR/python/orchestrator.py" \
  "$ROOT_DIR/python/analyze_results.py" \
  "$ROOT_DIR/python/plot_bound_comparison.py"

# Smoke-test: generate Lean candidates from a tiny synthetic JSON
TMP_DIR="$ROOT_DIR/.tmp_test"
rm -rf "$TMP_DIR"
mkdir -p "$TMP_DIR"
cat >"$TMP_DIR/top_near_misses.json" <<'JSON'
[
  {"score": 0.01, "a": [0.1, -0.2], "x0": 0.0, "v": 0.1, "gType": "gauss", "t0": 0.0, "tau": 0.5}
]
JSON

python - <<'PY'
from pathlib import Path
from python.analyze_results import generate_lean_candidates

tmp = Path(".tmp_test")
out = Path(".tmp_test") / "GeneratedCandidates.lean"
generate_lean_candidates(tmp, out, top_k=5)
text = out.read_text()
assert "structure Candidate" in text
assert "def topNearMisses" in text
PY

rm -rf "$TMP_DIR"

python - <<'PY'
import json
import math
from pathlib import Path

vertex_path = Path("mathematica/results/vertex.json")
assert vertex_path.exists(), "mathematica/results/vertex.json missing"
data = json.loads(vertex_path.read_text())

num_basis = int(data["numBasis"])
a = data["a"]
active_indices = data.get("activeIndices", [])
constraints = data.get("constraints", [])

assert len(a) == num_basis
assert isinstance(active_indices, list)
assert isinstance(constraints, list)
assert len(active_indices) == len(constraints) == 3, "expected 3 active AQEI constraints"

pi_quarter = math.pi ** 0.25
for idx, c in zip(active_indices, constraints):
  L = c["L"]
  B = float(c["B"])
  x0, v, t0, tau = c["params"]
  tau = float(tau)

  La = sum(float(li) * float(ai) for li, ai in zip(L, a))
  slack = La + B
  assert abs(slack) < 1e-9, f"active constraint not saturated: idx={idx} slack={slack}"

  # search.m uses Bmodel(g) = 0.1 * sqrt(∫ g(t)^2 dt); for an untruncated Gaussian,
  # ∫ g^2 = tau * sqrt(pi), hence B = 0.1 * sqrt(tau) * pi^(1/4)
  B_expected = 0.1 * math.sqrt(tau) * pi_quarter
  rel_err = abs(B - B_expected) / max(1e-12, abs(B_expected))
  assert rel_err < 5e-3, f"Bmodel mismatch: idx={idx} B={B} expected={B_expected} rel_err={rel_err}"

print("Vertex certificate tests: OK")
PY

python - <<'PY'
import math

from python.plot_bound_comparison import (
  b_fewster_2d_gaussian_benchmark,
  b_model,
)

# Sanity-check: proxy bound increases with tau on the model interval.
t1, t2 = 0.2, 0.8
assert b_model(t2) > b_model(t1)

# Sanity-check: analytic benchmark scales like 1/tau.
b1 = b_fewster_2d_gaussian_benchmark(t1)
b2 = b_fewster_2d_gaussian_benchmark(t2)
assert b1 > b2
ratio = (b1 * t1) / (b2 * t2)
assert abs(ratio - 1.0) < 1e-12

# Finite-domain truncation should be negligible in the tau-range used by search.m.
domain = 5.0
assert math.erf(domain / t2) > 0.999999

print("Bound comparison tests: OK")
PY

# Independent numerical verification of the vertex certificate.
# Re-integrates the active constraints with scipy and confirms L·a + B ≈ 0.
python "$ROOT_DIR/tools/verify_vertex.py" "$ROOT_DIR/mathematica/results/vertex.json"

# Smoke-test: analyze_results pipeline reports on available result files.
python -c "
import sys; sys.path.insert(0, '.')
from python.analyze_results import analyze_results
analyze_results()
"

# Smoke-test: plot_vertex_coefficients.py runs without crashing.
# Uses MPLBACKEND=Agg to avoid needing a display.
MPLBACKEND=Agg python -c "
import sys; sys.path.insert(0, '.')
from python.plot_vertex_coefficients import main
main()
print('plot_vertex_coefficients: OK')
"

echo "Python tests: OK"
