#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

cd "$ROOT_DIR"

# Fast test: small basis and constraint count.
# search.m reads these via Environment[] — see mathematica/search.m for defaults.
export AQEI_NUM_BASIS="2"
export AQEI_NUM_CONSTRAINTS="10"
export AQEI_DOMAIN="2.0"
export AQEI_SIGMA="0.7"
export AQEI_SEED="42"

# Redirect search.m output to a temp directory so it doesn't overwrite the
# certified vertex.json used by the Python and Lean test suites.
MATH_TMP=$(mktemp -d)
trap 'rm -rf "$MATH_TMP"' EXIT
export AQEI_RESULTS_DIR="$MATH_TMP"

# Prefer wolframscript; fall back to wolfram.
if command -v wolframscript >/dev/null 2>&1; then
  wolframscript -file "$ROOT_DIR/mathematica/search.m"
elif command -v wolfram >/dev/null 2>&1; then
  wolfram -script "$ROOT_DIR/mathematica/search.m"
else
  echo "ERROR: neither wolframscript nor wolfram found on PATH" >&2
  exit 1
fi

python - "$MATH_TMP/search_candidate.json" <<'PY'
import json, sys
from pathlib import Path

candidate_path = Path(sys.argv[1])
assert candidate_path.exists(), f"search_candidate.json missing at {candidate_path}"

data = json.loads(candidate_path.read_text())
assert "numBasis" in data, "search_candidate.json missing numBasis"
assert "a" in data, "search_candidate.json missing a"
assert len(data["a"]) == data["numBasis"]
assert "activeIndices" in data
assert "allConstraints" in data, "search_candidate.json missing allConstraints"
assert len(data["allConstraints"]) > 0, "allConstraints must be non-empty"

print(f"Mathematica tests: OK  (numBasis={data['numBasis']}, active={len(data['activeIndices'])}, allConstraints={len(data['allConstraints'])})")
PY
