#!/usr/bin/env python3

import math
from pathlib import Path

import matplotlib.pyplot as plt


def b_model(tau: float, *, domain: float = 5.0) -> float:
    # Matches mathematica/search.m:
    # g(t) = exp(-t^2/(2 tau^2)) (with t0=0), Bmodel = 0.1*sqrt(∫ g(t)^2 dt)
    # g(t)^2 = exp(-t^2/tau^2)
    integral = math.sqrt(math.pi) * tau * math.erf(domain / tau)
    return 0.1 * math.sqrt(integral)


def b_fewster_2d_gaussian_benchmark(tau: float) -> float:
    # Analytic benchmark for 1+1D massless scalar QEI (Fewster-style),
    # using the common form with squared sampling f(t)^2.
    # If we identify g(t) = f(t)^2 and set g(t)=exp(-t^2/(2 tau^2)), then
    # f(t)=exp(-t^2/(4 tau^2)) and the derivative-based bound scales like 1/tau.
    # We plot the resulting closed-form scaling constant for comparison only.
    return (math.sqrt(2.0 / math.pi) / 48.0) * (1.0 / tau)


def main() -> None:
    repo_root = Path(__file__).resolve().parents[1]
    out_path = repo_root / "papers" / "figures" / "bound_comparison.png"

    taus = [0.2 + i * (0.8 - 0.2) / 200.0 for i in range(201)]
    b_model_vals = [b_model(t) for t in taus]
    b_bench_vals = [b_fewster_2d_gaussian_benchmark(t) for t in taus]

    plt.figure(figsize=(6.5, 3.4))
    plt.plot(taus, b_model_vals, label=r"Proxy $B_{\mathrm{model}}(g)=0.1\,\|g\|_{L^2([-d,d])}$")
    plt.plot(taus, b_bench_vals, label=r"Analytic benchmark (Fewster-style) $\propto 1/\tau$")

    plt.xlabel(r"Gaussian width $\tau$")
    plt.ylabel(r"Bound magnitude $B$")
    plt.title("Bound comparison: proxy model vs analytic scaling")
    plt.legend(loc="best", fontsize=8)
    plt.tight_layout()

    out_path.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(out_path, dpi=200)
    plt.close()

    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
