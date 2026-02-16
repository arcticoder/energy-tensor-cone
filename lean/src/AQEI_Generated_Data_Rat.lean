/-- 
  AQEI_Generated_Data_Rat.lean
  Auto-generated from Phase 2 Optimization.
  Converted to exact Rationals for rigorous verification.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs

namespace AQEIGeneratedRat

/-- Vertex coefficients 'a' as Rationals -/
def coefficients : List Rat := [
  (-201930050 : Rat) / 188548783,
  (100 : Rat) / 1,
  (100 : Rat) / 1,
  (-697114919 : Rat) / 954338471,
  (271445287 : Rat) / 543764461,
  (100 : Rat) / 1,
]

/-- The normal vectors L for the active constraints (Rational approximation) -/
def active_L : List (List Rat) := [
  [
    (18242171 : Rat) / 185310433,
    (0 : Rat) / 1,
    (0 : Rat) / 1,
    (1686499 : Rat) / 783101748,
    (0 : Rat) / 1,
    (0 : Rat) / 1,
  ],
  [
    (-61 : Rat) / 489973282,
    (0 : Rat) / 1,
    (-33857 : Rat) / 815586094,
    (-7864737 : Rat) / 141838453,
    (-110132019 : Rat) / 383795849,
    (0 : Rat) / 1,
  ],
  [
    (-29649869 : Rat) / 504524770,
    (0 : Rat) / 1,
    (0 : Rat) / 1,
    (-188681736 : Rat) / 836755073,
    (-178 : Rat) / 269582495,
    (-320317 : Rat) / 94761543,
  ],
]

/-- The bounds B for the active constraints (Rational approximation) -/
def active_B : List Rat := [
  (92851846 : Rat) / 867769073,
  (83642891 : Rat) / 782481412,
  (31371962 : Rat) / 284241483,
]

end AQEIGeneratedRat

#print axioms AQEIGeneratedRat.coefficients
#print axioms AQEIGeneratedRat.active_L
#print axioms AQEIGeneratedRat.active_B

