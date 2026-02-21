(* mathematica/search.m
   Phase 2: Optimization-based Extreme Ray Search
   
   Generates a discrete set of AQEI constraints and solves a Linear Programming problem
   to find an extreme point (vertex) of the admissible set.

   Exports:
     - mathematica/results/vertex.json
*)

ClearAll["Global`*"];

(* Parameters *)
(* Default N=6/M=50 matches the certified vertex in lean/src/AQEI_Generated_Data_Rat.lean.
   Set AQEI_NUM_BASIS / AQEI_NUM_CONSTRAINTS env vars to override, e.g. for scaling
   experiments (N=100, M=500 was used for exploratory runs; see Limitations section). *)
numBasis = If[StringQ[Environment["AQEI_NUM_BASIS"]], ToExpression[Environment["AQEI_NUM_BASIS"]], 6];
numConstraints = If[StringQ[Environment["AQEI_NUM_CONSTRAINTS"]], ToExpression[Environment["AQEI_NUM_CONSTRAINTS"]], 50];
domain = If[StringQ[Environment["AQEI_DOMAIN"]], ToExpression[Environment["AQEI_DOMAIN"]], 5.0];
σ = If[StringQ[Environment["AQEI_SIGMA"]], ToExpression[Environment["AQEI_SIGMA"]], 0.5];

(* Reproducible fixed seed.  The certified vertex.json was generated with seed 42.
   Override by setting AQEI_SEED in the environment. *)
rawSeed = If[StringQ[Environment["AQEI_SEED"]], ToExpression[Environment["AQEI_SEED"]], 42];
SeedRandom[rawSeed];
Print["Seed: ", rawSeed, "  numBasis: ", numBasis, "  numConstraints: ", numConstraints];

resultsDir = With[{env = Environment["AQEI_RESULTS_DIR"]},
  If[env === $Failed || env === "",
    FileNameJoin[{DirectoryName[$InputFileName], "results"}],
    env]];
If[!DirectoryQ[resultsDir], CreateDirectory[resultsDir]];

(* --- 1. Define Basis --- *)
centers = Table[{RandomReal[{-domain, domain}], RandomReal[{-domain, domain}]}, {i, numBasis}];

(* Random symmetric matrices for the basis spin-2 components *)
basisS = Table[
  Module[{m = {{RandomReal[{-1, 1}], RandomReal[{-1, 1}]}, {RandomReal[{-1, 1}], RandomReal[{-1, 1}]}}},
    (m + Transpose[m])/2
  ],
  {i, numBasis}
];

phi[{t_, x_}, {tc_, xc_}] := Exp[-((t - tc)^2 + (x - xc)^2)/(2 σ^2)];

eta = DiagonalMatrix[{-1, 1}];

normalizeVelocity[v_] := Module[{uUnnorm = {1, v}, norm},
  norm = Sqrt[Abs[-uUnnorm . eta . uUnnorm]];
  uUnnorm/norm
];

(* --- 2. Define Constraint Generation --- *)

(* Precompute integrals for basis element i along worldline (x0, v) with sampling g *)
computeL[i_, x0_, v_, gFunc_] := Module[{u, integrand},
  u = normalizeVelocity[v];
  integrand[t_] := Module[{pos = {t, x0 + v t}, val},
    (* val = u . (phi_i(pos) * S_i) . u *)
    val = (u . basisS[[i]] . u) * phi[pos, centers[[i]]] * gFunc[t];
    val
  ];
  (* PrecisionGoal->12 targets ~10^-12 relative error; combined with the Gaussian
     decay (tails below 10^-30 at ±10σ) this keeps L_i float errors well below 10^-10,
     consistent with the active_B_tight rationalization precision in the Lean proof. *)
  Quiet@NIntegrate[integrand[t], {t, -domain, domain},
    Method -> "GlobalAdaptive", MaxRecursion -> 15, PrecisionGoal -> 12]
];

(* Bound B >= 0. Inequality is L.a >= -B *)
Bmodel[gFunc_] := 0.1 * Sqrt[Quiet@NIntegrate[gFunc[t]^2, {t, -domain, domain},
  Method -> "GlobalAdaptive", MaxRecursion -> 15, PrecisionGoal -> 12]];

gGaussian[t_, t0_, τ_] := Exp[-(t - t0)^2/(2 τ^2)];

GenerateConstraint[] := Module[{x0, v, t0, τ, gFunc, Lvec, Bval},
  x0 = RandomReal[{-domain, domain}];
  v = RandomReal[{-0.9, 0.9}];
  t0 = RandomReal[{-domain/2, domain/2}];
  τ = RandomReal[{0.2, 0.8}];
  gFunc = Function[t, gGaussian[t, t0, τ]];
  
  Lvec = Table[computeL[i, x0, v, gFunc], {i, numBasis}];
  Bval = Bmodel[gFunc];
  
  (* Return as Association *)
  <| "L" -> Lvec, "B" -> Bval, "params" -> {x0, v, t0, τ} |>
];

Print["Generating ", numConstraints, " constraints..."];
constraints = Table[GenerateConstraint[], {numConstraints}];

(* Matrix M and vector b for M.a >= b *)
(* Condition: L.a >= -B  =>  L.a >= -B *)
matrixM = constraints[[All, "L"]];
vectorB = -constraints[[All, "B"]];

(* --- 3. Linear Programming --- *)
(* Objective: Minimize Energy density at origin. T_00. *)
centerOrigin = {0.0, 0.0};
objectiveRows = Table[
  Module[{base, pert},
    (* T_00 component of basis i at origin *)
    base = (phi[centerOrigin, centers[[i]]] * basisS[[i]])[[1, 1]];
    (* Small seeded perturbation to break LP degeneracy.
       Deterministic because SeedRandom was called earlier. *)
    pert = RandomReal[{-0.01, 0.01}];
    <| "base" -> base, "total" -> base + pert |>
  ],
  {i, numBasis}
];
objectiveCBase = objectiveRows[[All, "base"]];
objectiveC      = objectiveRows[[All, "total"]];

(* LinearProgramming[c, m, b] minimizes c.x subject to m.x >= b *)
Print["Solving Linear Programming problem..."];

(* Add generic large box constraints to ensure boundedness *)
(* -100 <= a_i <= 100 *)
largeBound = 100.0;
solutionA = LinearProgramming[
  objectiveC,
  matrixM,
  vectorB, 
  ConstantArray[{-largeBound, largeBound}, numBasis] 
];

Print["Solution a: ", solutionA];

(* --- 4. Identify Active Constraints --- *)
(* Active if L.a + B approx 0 *)
slacks = (matrixM . solutionA) - vectorB; (* Should be >= 0 *)
tolerance = 10^-5;
activeIndices = Flatten[Position[slacks, s_ /; Abs[s] < tolerance]];

(* Check if box limits are active *)
boxActive = False;
Do[
  If[Abs[Abs[solutionA[[i]]] - largeBound] < tolerance, boxActive = True], 
  {i, numBasis}
];

Print["Number of active AQEI constraints: ", Length[activeIndices]];
Print["Active constraint indices: ", activeIndices];
Print["Box constraints active? ", boxActive];

(* Only export if we found AQEI activity (otherwise we just hit the box) *)
(* In a real run we might need more constraints or careful objective tuning *)

(* --- 5. Export --- *)
(* Full dataset: always written to search_candidate.json.
   This is the raw search output for reproducibility audits and inactive-
   constraint checks.  It is NOT the certified artifact and is gitignored. *)
(* Serialize constraints to plain numeric lists for JSON export.
   Force N[] evaluation to prevent any symbolic or pattern remnants from
   unevaluated sub-expressions (e.g. from gFunc closures) leaking into the
   output and causing Export::jsonstrictencoding errors. *)
serializeConstraint[c_] := <|
  "L"      -> N[c["L"]],
  "B"      -> N[c["B"]],
  "params" -> N[c["params"]]
|>;

candidateData = <|
  "numBasis"       -> numBasis,
  "basisS"         -> N[basisS],
  "centers"        -> N[centers],
  "a"              -> N[solutionA],
  "objectiveC"     -> N[objectiveCBase],
  "activeIndices"  -> activeIndices,
  "constraints"    -> serializeConstraint /@ constraints[[activeIndices]],
  "allConstraints" -> serializeConstraint /@ constraints
|>;

Export[FileNameJoin[{resultsDir, "search_candidate.json"}], candidateData, "JSON"];
Print["Search results exported to search_candidate.json"];

(* vertex.json is the certified artifact linking the float search to the
   Lean formal proof.  Only write it if it does not already exist in this
   results directory, so that the committed certified copy is never silently
   overwritten by a fresh search run.  Set AQEI_FORCE_OVERWRITE=1 to
   regenerate it intentionally (e.g. after updating the Lean certificate). *)
vertexJson = FileNameJoin[{resultsDir, "vertex.json"}];
forceOverwrite = StringQ[Environment["AQEI_FORCE_OVERWRITE"]] && (Environment["AQEI_FORCE_OVERWRITE"] != "");
If[!FileExistsQ[vertexJson] || forceOverwrite,
  vertexData = <|
    "numBasis"      -> numBasis,
    "basisS"        -> N[basisS],
    "centers"       -> N[centers],
    "a"             -> N[solutionA],
    "activeIndices" -> activeIndices,
    "constraints"   -> serializeConstraint /@ constraints[[activeIndices]]
  |>;
  Export[vertexJson, vertexData, "JSON"];
  Print["Certified vertex exported to vertex.json"],
  Print["vertex.json already exists — skipping overwrite."]
  Print["  (Set AQEI_FORCE_OVERWRITE=1 to regenerate the certified artifact.)"]
];
