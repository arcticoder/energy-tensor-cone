#!/bin/bash
# refresh-supplements.sh — Regenerate the journal supplements archive.
# Run from the repo root after any change to source files.
set -euo pipefail

tar -czf supplements/energy-tensor-cone-supplements.tar.gz \
  lean/lakefile.lean \
  lean/lake-manifest.json \
  lean/lean-toolchain \
  lean/test_polyhedral.lean \
  lean/src/*.lean \
  mathematica/search.m mathematica/results/vertex.json \
  python/__init__.py python/analyze_results.py python/orchestrator.py \
  python/plot_bound_comparison.py python/plot_vertex_coefficients.py \
  tools/generate_lean_data.py \
  tools/generate_lean_data_rat.py \
  tools/translate_vertex.py \
  tools/verify_vertex.py \
  tests/*.sh run_tests.sh \
  README.md supplements/README-supplements.md

echo "Supplements refreshed: supplements/energy-tensor-cone-supplements.tar.gz"
tar tzf supplements/energy-tensor-cone-supplements.tar.gz | wc -l
echo "files."
