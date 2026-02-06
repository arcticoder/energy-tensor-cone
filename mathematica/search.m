(* mathematica/search.m
   1+1 model: t,x coordinates. Metric signature (-,+).
   T modeled as sum_i a_i phi_i(t,x) S_i, with S_i 2x2 symmetric matrices.
   For worldlines gamma(t) = (t, x0 + v t), u = gamma'(t) normalized.

   Exports:
     - mathematica/results/summary.json
     - mathematica/results/top_near_misses.json  (top 5 smallest nonnegative scores)
     - mathematica/results/near_misses.json      (all near-misses)
     - mathematica/results/violations.json       (all violations)
*)

ClearAll["Global`*"];

(* Allow fast test overrides via environment variables *)
getEnvInt[name_, default_] := Module[{v = Environment[name]}, If[v === $Failed || v === "", default, ToExpression[v]]];
getEnvReal[name_, default_] := Module[{v = Environment[name]}, If[v === $Failed || v === "", default, ToExpression[v]]];

(* Parameters *)
numBasis = getEnvInt["AQEI_NUM_BASIS", 6];
numTrials = getEnvInt["AQEI_NUM_TRIALS", 20000];
domain = getEnvReal["AQEI_DOMAIN", 5.0];
σ = getEnvReal["AQEI_SIGMA", 0.5];

SeedRandom[1234];

(* Where to write results *)
scriptDir = DirectoryName[$InputFileName];
resultsDir = FileNameJoin[{scriptDir, "results"}];
If[!DirectoryQ[resultsDir], CreateDirectory[resultsDir]];

(* Basis centers and matrices *)
centers = Table[{RandomReal[{-domain, domain}], RandomReal[{-domain, domain}]}, {i, numBasis}];

basisS = Table[
  Module[{m = {{RandomReal[{-1, 1}], RandomReal[{-1, 1}]}, {RandomReal[{-1, 1}], RandomReal[{-1, 1}]}}},
    (m + Transpose[m])/2
  ],
  {i, numBasis}
];

phi[{t_, x_}, {tc_, xc_}] := Exp[-((t - tc)^2 + (x - xc)^2)/(2 σ^2)];

TComponents[a_List][{t_, x_}] := Module[{sum = ConstantArray[0., {2, 2}]},
  Do[sum += a[[i]]*phi[{t, x}, centers[[i]]]*basisS[[i]], {i, numBasis}];
  sum
];

eta = DiagonalMatrix[{-1, 1}];

normalizeVelocity[v_] := Module[{uUnnorm = {1, v}, norm},
  (* u.u = -1 in (-,+) convention; handle numeric abs for stability *)
  norm = Sqrt[Abs[-uUnnorm . eta . uUnnorm]];
  uUnnorm/norm
];

(* Sampling functions g(t) — Gaussians / approx-compact support *)
gGaussian[t_, t0_, τ_] := Exp[-(t - t0)^2/(2 τ^2)];

(* Smooth compact-ish bump via tanh edges *)
gCompact[t_, t0_, τ_] := (Tanh[(t - (t0 - τ))/0.01] - Tanh[(t - (t0 + τ))/0.01])/2;

(* AQEI model bound B_{γ,g} — placeholder demo model; replace with known bound if available *)
Bmodel[gFunc_] := 0.1*Sqrt[NIntegrate[gFunc[t]^2, {t, -Infinity, Infinity}, Method -> "GlobalAdaptive", MaxRecursion -> 10]];

IofT[a_List, x0_, v_, gFunc_] := Module[{u, integrand},
  u[t_] := normalizeVelocity[v];
  integrand[t_] := Module[{pos = {t, x0 + v t}, Tmat, uu},
    Tmat = TComponents[a][pos];
    uu = u[t];
    uu . Tmat . uu * gFunc[t]
  ];
  NIntegrate[integrand[t], {t, -domain, domain}, Method -> "GlobalAdaptive", MaxRecursion -> 12]
];

(* Score: negative => violation; small nonnegative => near-miss *)
score[a_List, x0_, v_, gFunc_] := Module[{I, B},
  I = IofT[a, x0, v, gFunc];
  B = Bmodel[gFunc];
  I + B
];

RandomTrial[] := Module[{a, x0, v, gType, t0, τ, gFunc, val},
  a = RandomReal[{-2, 2}, numBasis];
  x0 = RandomReal[{-domain, domain}];
  v = RandomReal[{-0.9, 0.9}];
  gType = If[RandomReal[] < 0.5, "gauss", "compact"];
  t0 = RandomReal[{-domain/2, domain/2}];
  τ = RandomReal[{0.1, 1.0}];
  gFunc = If[gType === "gauss",
    Function[t, gGaussian[t, t0, τ]],
    Function[t, gCompact[t, t0, τ]]
  ];
  val = score[a, x0, v, gFunc];
  <|
    "score" -> val,
    "a" -> a,
    "x0" -> x0,
    "v" -> v,
    "gType" -> gType,
    "t0" -> t0,
    "tau" -> τ
  |>
];

Print["Running trials: ", numTrials, " (basis=", numBasis, ")"];

(* Robust parallelization: just compute trials in parallel, then filter *)
If[$KernelCount > 1,
  trials = ParallelTable[RandomTrial[], {i, numTrials}],
  trials = Table[RandomTrial[], {i, numTrials}]
];

violations = Select[trials, #score < 0.0 &];
nearMisses = Select[trials, 0.0 <= #score < 0.05 &];

sortedNear = SortBy[nearMisses, #score &];
topNear = Take[sortedNear, UpTo[5]];

Print["Violations found: ", Length[violations]];
Print["Near-misses found: ", Length[nearMisses]];

Export[FileNameJoin[{resultsDir, "violations.json"}], violations, "JSON"];
Export[FileNameJoin[{resultsDir, "near_misses.json"}], nearMisses, "JSON"];
Export[FileNameJoin[{resultsDir, "top_near_misses.json"}], topNear, "JSON"];

Export[FileNameJoin[{resultsDir, "summary.json"}], <|
  "numBasis" -> numBasis,
  "numTrials" -> numTrials,
  "domain" -> domain,
  "sigma" -> σ,
  "violations" -> Length[violations],
  "nearMisses" -> Length[nearMisses]
|>, "JSON"];
