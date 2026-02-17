import Lake
open Lake DSL

package warpConeAqei where
  -- Keep the package lean: no external deps by default.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

lean_lib WarpConeAqei where
  srcDir := "src"
  roots := #[`AQEI, `StressEnergy, `Lorentz, `WarpConeAqei]
