/-- 
  AQEI_Generated_Data.lean
  Auto-generated from Phase 2 Optimization (Mathematica -> Python).
  Contains the concrete basis, vertex coefficients, and active constraints.
-/

namespace AQEIGenerated

/-- Centers of the Gaussian basis functions (t, x) -/
def basis_centers : List (Float × Float) := [
  (3.7660849257419287, 0.21964250201877178),
  (-4.137765730458675, -1.2208704569511415),
  (-4.883554270307533, 4.27266163342162),
  (0.43756766951068116, -0.20668329527575402),
  (-2.5465077221929526, 2.59896001561588),
  (4.849929975443043, -2.8295487843666134),
]

/-- Spin-2 polarization matrices for the basis -/
def basis_matrices : List (List (List Float)) := [
  [[-0.08196562614982383, 0.46858345469510176], [0.46858345469510176, -0.4720536649999394]],
  [[0.8391203247282579, 0.4111255345634237], [0.4111255345634237, 0.17588531238907024]],
  [[-0.8343902132101433, 0.4863735633418209], [0.4863735633418209, 0.5037324677170889]],
  [[-0.19690154632734114, 0.4571359784915543], [0.4571359784915543, -0.7889233157136943]],
  [[-0.05747670110263359, 0.09180181814428501], [0.09180181814428501, -0.5672639397142523]],
  [[-0.5767939044480208, 0.2875284500791686], [0.2875284500791686, 0.35735232771114855]],
]

/-- Vertex coefficients 'a' found by Linear Programming -/
def coefficients : List Float := [
  -1.0709697871664332,
  100.0,
  100.0,
  -0.7304692624091018,
  0.49919644711756916,
  99.99999999999997,
]

/-- Indices of active constraints (1-based from Mathematica) -/
def active_indices : List Nat := [23, 27, 50]

structure ConstraintData where
  x0 : Float
  v : Float
  t0 : Float
  tau : Float
deriving Repr

/-- Parameters for the active constraints -/
def active_constraints : List ConstraintData := [
  { x0 := -1.9991853305023106, v := 0.7361223553664695, t0 := 2.182178299553426, tau := 0.6459483784290181 },
  { x0 := 1.2557879554539433, v := -0.8779684965162651, t0 := -0.9508678180666088, tau := 0.6446664585879505 },
  { x0 := 1.6610542586582824, v := -0.8749207972638751, t0 := 2.1155521196619365, tau := 0.687279680482233 },
]

end AQEIGenerated
