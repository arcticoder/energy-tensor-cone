import subprocess
import sys
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
# Ensure the project root is on sys.path so `from python.X import` works
# regardless of the working directory from which this script is invoked.
sys.path.insert(0, str(ROOT))
MATH_FILE = ROOT / "mathematica" / "search.m"
RESULT_DIR = ROOT / "mathematica" / "results"
LEAN_DIR = ROOT / "lean"


def _find_wolfram_command() -> list[str]:
    """Return a command prefix to run a Wolfram Language script headlessly."""
    # Prefer wolframscript if present; otherwise fall back to the wolfram CLI.
    probes: list[tuple[str, list[str]]] = [
        ("wolframscript", ["wolframscript", "-file"]),
        ("wolfram", ["wolfram", "-script"]),
    ]
    for exe, prefix in probes:
        try:
            subprocess.run([exe, "-version"], check=True, capture_output=True, text=True)
            return prefix
        except Exception:
            continue

    raise RuntimeError("Neither 'wolframscript' nor 'wolfram' appears runnable on PATH.")


def run_mathematica(env: dict[str, str] | None = None) -> None:
    print("Running Mathematica search (headless)...")
    cmd_prefix = _find_wolfram_command()
    cmd = cmd_prefix + [str(MATH_FILE)]
    subprocess.run(cmd, check=True, cwd=str(ROOT), env=env)
    print("Mathematica finished.")


def analyze_results() -> None:
    from python.analyze_results import generate_lean_candidates

    summary = RESULT_DIR / "summary.json"
    if summary.exists():
        s = json.loads(summary.read_text())
        print("Mathematica summary:", s)
    else:
        print("No summary.json found.")

    generate_lean_candidates(
        results_dir=RESULT_DIR,
        out_file=LEAN_DIR / "src" / "GeneratedCandidates.lean",
        top_k=5,
    )


def run_lean_build() -> None:
    print("Running lake build (Lean 4)...")
    subprocess.run(["lake", "build"], check=True, cwd=str(LEAN_DIR))
    print("Lean build finished.")


if __name__ == "__main__":
    run_mathematica()
    analyze_results()
    run_lean_build()
