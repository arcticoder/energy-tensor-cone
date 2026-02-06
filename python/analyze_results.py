import json
from pathlib import Path


def _as_lean_string(s: str) -> str:
    return '"' + s.replace('\\', '\\\\').replace('"', '\\"') + '"'


def _as_lean_float(x) -> str:
    # Lean's Float literals accept standard decimal / scientific notation.
    if isinstance(x, (int, float)):
        return repr(float(x))
    return repr(float(x))


def generate_lean_candidates(results_dir: Path, out_file: Path, top_k: int = 5) -> None:
    """Convert Mathematica JSON output into a Lean file with candidate data.

    This is intentionally data-only; semantics are added later when a finite basis model
    of StressEnergy is formalized.
    """
    results_dir = Path(results_dir)
    out_file = Path(out_file)

    top_path = results_dir / "top_near_misses.json"
    if not top_path.exists():
        raise FileNotFoundError(f"Missing {top_path}")

    data = json.loads(top_path.read_text())
    data = list(data)[:top_k]

    out_file.parent.mkdir(parents=True, exist_ok=True)

    lines: list[str] = []
    lines.append("/-- Auto-generated from Mathematica results. -/")
    lines.append("import Std")
    lines.append("")
    lines.append("structure Candidate where")
    lines.append("  score : Float")
    lines.append("  a : Array Float")
    lines.append("  x0 : Float")
    lines.append("  v : Float")
    lines.append("  gType : String")
    lines.append("  t0 : Float")
    lines.append("  tau : Float")
    lines.append("deriving Repr")
    lines.append("")

    cand_exprs: list[str] = []
    for item in data:
        a_list = item.get("a", [])
        a_arr = "#[]" if not a_list else "#[(" + "), (".join(_as_lean_float(x) for x in a_list) + ")]"
        cand_exprs.append(
            "{ score := "
            + _as_lean_float(item.get("score", 0.0))
            + ", a := "
            + a_arr
            + ", x0 := "
            + _as_lean_float(item.get("x0", 0.0))
            + ", v := "
            + _as_lean_float(item.get("v", 0.0))
            + ", gType := "
            + _as_lean_string(str(item.get("gType", "")))
            + ", t0 := "
            + _as_lean_float(item.get("t0", 0.0))
            + ", tau := "
            + _as_lean_float(item.get("tau", 0.0))
            + " }"
        )

    lines.append("def topNearMisses : List Candidate :=")
    if not cand_exprs:
        lines.append("  []")
    else:
        lines.append("  [")
        for i, expr in enumerate(cand_exprs):
            comma = "," if i + 1 < len(cand_exprs) else ""
            lines.append("    " + expr + comma)
        lines.append("  ]")

    out_file.write_text("\n".join(lines) + "\n")
    print(f"Wrote {out_file}")
