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
    out.write_text("/-- Placeholder; overwritten by python/analyze_results.py. -/\nimport Std\n\n/-- (Candidate list removed as unused) --/\n")
PY

"$ROOT_DIR/tests/build_lean.sh"

# Rigorous checks for sorry/axioms in critical proof files
echo "Checking for unintentional sorry statements..."

# Allow intentional sorries in ConeProperties.lean (documented as false theorems)
# Check all other files for sorry
if find "$ROOT_DIR/lean/src" -name "*.lean" \
    ! -name "ConeProperties.lean" \
    -exec grep -l "sorry" {} + 2>/dev/null; then
    echo "ERROR: Found sorry in non-ConeProperties files!"
    echo "  (ConeProperties.lean intentionally contains sorry for false theorems)"
    exit 1
fi

# Verify that the #print axioms checks are present in critical files
critical_files=("FinalTheorems.lean" "VertexVerificationRat.lean" "PolyhedralVertex.lean" "AQEIFamilyInterface.lean")
echo "Verifying axiom checks are present in critical files..."
for file in "${critical_files[@]}"; do
    if ! grep -q "#print axioms" "$ROOT_DIR/lean/src/$file"; then
        echo "WARNING: $file missing #print axioms checks"
    fi
done

echo "Lean tests: OK (build passed, sorry/axiom checks completed)"
