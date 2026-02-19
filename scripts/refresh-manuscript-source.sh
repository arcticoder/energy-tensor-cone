#!/bin/bash
# refresh-manuscript-source.sh — Regenerate papers/manuscript-source.zip.
# Run from the repo root after editing any LaTeX source files in papers/.
set -euo pipefail

ZIP=papers/manuscript-source.zip

rm -f "$ZIP"

zip -j "$ZIP" \
  papers/aqei-cone-formalization.tex \
  papers/aqei-cone-formalization-body.tex \
  papers/aqei-cone-formalization-prd.tex \
  papers/common-preamble.tex \
  papers/common-theorems.tex \
  papers/aqei-cone-formalization.bib \
  papers/iopjournal.cls

zip "$ZIP" papers/figures/bound_comparison.png papers/figures/vertex_coefficients.png

echo "Manuscript source refreshed: $ZIP"
unzip -l "$ZIP"
