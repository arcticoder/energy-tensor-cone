import Lake
open Lake DSL

package warpConeAqei where
  -- Keep the package lean: no external deps by default.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

@[default_target]
lean_lib WarpConeAqei where
  srcDir := "src"
  roots := #[
    `Lorentz,
    `StressEnergy,
    `AQEI,
    `ExtremeRays,
    `AffineToCone,
    `AQEIFamilyInterface,
    `AQEIToInterface,
    `ConeProperties,
    `PolyhedralVertex,
    `FiniteToyModel,
    `AQEI_Generated_Data,
    `AQEI_Generated_Data_Rat,
    `GeneratedCandidates,
    `VertexVerificationRat,
    `VertexVerification,
    `FinalTheorems,
    `WarpConeAqei
  ]
