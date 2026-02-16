#!/bin/bash
tar -czf supplements/energy-tensor-cone-supplements.tar.gz \
  lean/src/*.lean \
  mathematica/search.m mathematica/results/*.json \
  python/*.py \
  tests/*.sh run_tests.sh \
  README.md supplements/README-supplements.md
echo "Supplements refreshed."
