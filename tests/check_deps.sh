#!/usr/bin/env bash
# check_deps.sh — Verify that required tools are installed before running tests.
# Run this once after cloning to confirm your environment is ready.
set -euo pipefail

OK=1

echo "=== Checking dependencies ==="

# --- Lean / elan ---
if command -v lake &>/dev/null; then
    echo "[OK] lake: $(lake --version 2>/dev/null || echo 'found')"
elif command -v elan &>/dev/null; then
    echo "[WARN] elan found but 'lake' not in PATH. Run: source ~/.elan/env"
    OK=0
else
    echo "[MISSING] elan/lake not found."
    echo "  Install: curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y"
    echo "  Then: source ~/.elan/env"
    OK=0
fi

# --- Python ---
if command -v python3 &>/dev/null || command -v python &>/dev/null; then
    PY=$(command -v python3 || command -v python)
    echo "[OK] Python: $("$PY" --version 2>&1)"
else
    echo "[MISSING] Python 3 not found."
    OK=0
fi

# --- Python packages ---
for pkg in scipy matplotlib numpy; do
    if "$PY" -c "import $pkg" 2>/dev/null; then
        echo "[OK] Python package: $pkg"
    else
        echo "[MISSING] Python package: $pkg"
        echo "  Install: pip install $pkg"
        OK=0
    fi
done

# --- Python project package ---
if "$PY" -c "import python" 2>/dev/null; then
    echo "[OK] python package (local) installed"
else
    echo "[MISSING] Local python package not installed."
    echo "  Install: pip install -e python/"
    OK=0
fi

# --- Mathematica (optional) ---
if command -v wolframscript &>/dev/null; then
    echo "[OK] wolframscript: found (Mathematica tests will run)"
else
    echo "[INFO] wolframscript not found — Mathematica tests will be skipped"
fi

echo ""
if [[ "$OK" -eq 1 ]]; then
    echo "All required dependencies present. Run: ./run_tests.sh"
else
    echo "Some dependencies are missing. Install them and re-run this script."
    exit 1
fi
