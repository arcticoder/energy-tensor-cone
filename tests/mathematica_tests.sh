#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

cd "$ROOT_DIR"

# Keep this fast.
export AQEI_NUM_TRIALS="200"
export AQEI_NUM_BASIS="2"
export AQEI_DOMAIN="2.0"
export AQEI_SIGMA="0.7"

# Prefer wolframscript; fall back to wolfram.
if command -v wolframscript >/dev/null 2>&1; then
  wolframscript -file "$ROOT_DIR/mathematica/search.m"
elif command -v wolfram >/dev/null 2>&1; then
  wolfram -script "$ROOT_DIR/mathematica/search.m"
else
  echo "ERROR: neither wolframscript nor wolfram found on PATH" >&2
  exit 1
fi

python - <<'PY'
import json
from pathlib import Path

results = Path("mathematica/results")
summary = results / "summary.json"
top = results / "top_near_misses.json"

assert summary.exists(), "summary.json missing"
assert top.exists(), "top_near_misses.json missing"

s = json.loads(summary.read_text())
assert "numTrials" in s and s["numTrials"] == 200

t = json.loads(top.read_text())
assert isinstance(t, list)
print("Mathematica tests: OK")
PY
