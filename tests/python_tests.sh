#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

cd "$ROOT_DIR"

python -m py_compile \
  "$ROOT_DIR/python/orchestrator.py" \
  "$ROOT_DIR/python/analyze_results.py"

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

echo "Python tests: OK"
