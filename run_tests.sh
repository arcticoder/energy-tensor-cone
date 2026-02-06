#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

"$ROOT_DIR/tests/python_tests.sh"
"$ROOT_DIR/tests/mathematica_tests.sh"
"$ROOT_DIR/tests/lean_tests.sh"

echo "All tests passed."
