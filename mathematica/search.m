(* mathematica/search.m
   Phase 2: Optimization-based Extreme Ray Search
   
   Generates a discrete set of AQEI constraints and solves a Linear Programming problem
   to find an extreme point (vertex) of the admissible set.

   Exports:
     - mathematica/results/vertex.json
*)

ClearAll["Global`*"];

(* Parameters *)
numBasis = 6;
numConstraints = 50; (* Number of random worldline constraints *)
domain = 5.0;
σ = 0.5;

SeedRandom[1234];

resultsDir = FileNameJoin[{DirectoryName[$InputFileName], "results"}];
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
  Quiet@NIntegrate[integrand[t], {t, -domain, domain}, Method -> "GlobalAdaptive", MaxRecursion -> 10]
];

(* Bound B >= 0. Inequality is L.a >= -B *)
Bmodel[gFunc_] := 0.1 * Sqrt[Quiet@NIntegrate[gFunc[t]^2, {t, -domain, domain}]];

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
objectiveC = Table[
  Module[{val},
    (* T_00 component of basis i at origin *)
    val = (phi[centerOrigin, centers[[i]]] * basisS[[i]])[[1, 1]];
    (* Add small random perturbation to avoid degeneracy *)
    val + RandomReal[{-0.01, 0.01}]
  ], 
  {i, numBasis}
];

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
vertexData = <|
  "numBasis" -> numBasis,
  "basisS" -> basisS,
  "centers" -> centers,
  "a" -> solutionA,
  "activeIndices" -> activeIndices,
  "constraints" -> constraints[[activeIndices]]
|>;

Export[FileNameJoin[{resultsDir, "vertex.json"}], vertexData, "JSON"];
Print["Results exported to vertex.json"];
