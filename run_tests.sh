#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Ensure Lean project builds first
"$ROOT_DIR/tests/build_lean.sh"

echo "Running sanity checks..."
python3 "$ROOT_DIR/python/sanity_checks.py"

echo "Verifying rational values..."
python3 "$ROOT_DIR/python/check_rational_values.py"

"$ROOT_DIR/tests/python_tests.sh"
"$ROOT_DIR/tests/mathematica_tests.sh"
"$ROOT_DIR/tests/lean_tests.sh"

echo "All tests passed."
