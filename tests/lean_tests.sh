#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

cd "$ROOT_DIR"

# Ensure we have a GeneratedCandidates.lean (tests expect the file to exist).
python - <<'PY'
from pathlib import Path

out = Path("lean/src/GeneratedCandidates.lean")
out.parent.mkdir(parents=True, exist_ok=True)
if not out.exists():
    out.write_text("/-- Placeholder; overwritten by python/analyze_results.py. -/\nimport Std\n\nstructure Candidate where\n  score : Float\n  a : Array Float\n  x0 : Float\n  v : Float\n  gType : String\n  t0 : Float\n  tau : Float\nderiving Repr\n\ndef topNearMisses : List Candidate := []\n")
PY

"$ROOT_DIR/tests/build_lean.sh"

echo "Lean tests: OK"
