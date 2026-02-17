## BLOCKED: Analytic bound comparison + “<5% deviation” claim

**Why blocked:**
- The placeholder expression $B = \frac{1}{2\pi}\int \frac{|\hat g(\omega)|^2}{\omega^2}\,d\omega$ and the draft Mathematica snippet in TODO do not match the toy proxy-bound model implemented in `mathematica/search.m`.
- The current repository does not define a physically correct $T(\gamma(t))(u(t),u(t))$ for which a state-independent Fewster bound can be computed and meaningfully compared.
- As a result, we cannot responsibly claim “scores saturate close to Fewster’s bound” or “max deviation <5%” without first specifying the underlying QFT model, sampling normalization conventions, and a bound formula consistent with those choices.

**What is already in place (partial progress):**
- The manuscript contains a Fewster-style Fourier-space inequality statement for context.
- The paper includes a proxy-bound vs. benchmark scaling figure (`papers/figures/bound_comparison.png`).
- **NEW (2026-02-16)**: Implemented toy QFT functionals in `lean/src/AQEI.lean`:
  - `AQEI_functional_toy`: Discrete Riemann sum approximation of ∫ T(γ(t))(u(t), u(t)) · g(t) dt
  - `AQEI_bound_toy`: Fourier-space bound discretization ∫ |ĝ(ω)|²/ω² dω
  - These provide computable models for finite basis systems bridging to Python/Mathematica

**Unblock prerequisites:**
1. ✅ **PARTIALLY COMPLETE**: Toy stress-energy functionals now specified in Lean (see AQEI_functional_toy)
2. Derive/choose an analytic bound formula consistent with that model + the Gaussian sampling used
3. Implement the comparison (Mathematica or Python) and add tests that compute the claimed deviation threshold.
