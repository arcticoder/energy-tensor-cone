import AQEI_Generated_Data

namespace Phase2

open AQEIGenerated

/--
  VertexVerification.lean

  We verify that the point found by optimization is indeed a vertex of the polytope
  defined by the intersection of the AQEI half-spaces and the box constraints.

  A point `v` in R^n is a vertex if it sits at the intersection of `n` linearly
  independent hyperplanes (active constraints).

  Here n=6. We have observed:
  - 3 active AQEI constraints.
  - 3 active box constraints (hitting the upper bound 100.0).
-/

-- Simple Matrix Utilities for Float
section LinearAlgebra

abbrev Row := List Float
abbrev Matrix := List Row

def dot (v1 v2 : Row) : Float :=
  List.zipWith (· * ·) v1 v2 |>.foldl (· + ·) 0.0

def scale (c : Float) (v : Row) : Row :=
  v.map (c * ·)

def add (v1 v2 : Row) : Row :=
  List.zipWith (· + ·) v1 v2

-- Subtract projection of pivot from row
def eliminate (pivot : Row) (row : Row) (col_idx : Nat) : Row :=
  match pivot.get? col_idx, row.get? col_idx with
  | some p_val, some r_val =>
    if p_val.abs < 1e-12 then row -- pivot too small, skip
    else
      let factor := r_val / p_val
      List.zipWith (fun r p => r - factor * p) row pivot
  | _, _ => row

-- Very simple Gaussian elimination to check for linear independence
-- Returns the number of non-zero rows (rank)
def compute_rank (m : Matrix) (tolerance : Float := 1e-9) : Nat :=
  let n_rows := m.length
  let n_cols := match m.head? with | some r => r.length | none => 0

  -- Recursive elimination
  let rec reduce (rows : Matrix) (c : Nat) (rank_acc : Nat) : Nat :=
    if c >= n_cols || rows.isEmpty then rank_acc
    else
      -- Find pivot in current column `c`
      let pivot_idx_opt := rows.findIdx? (fun r => match r.get? c with | some v => v.abs > tolerance | none => false)

      match pivot_idx_opt with
      | none =>
        -- No pivot in this column, move to next column
        reduce rows (c + 1) rank_acc
      | some pivot_idx =>
        -- Move pivot to top
        let pivot := rows.get! pivot_idx
        let other_rows := rows.eraseIdx pivot_idx

        -- Eliminate this column from other rows
        let new_rows := other_rows.map (fun r => eliminate pivot r c)

        -- Continue
        reduce new_rows (c + 1) (rank_acc + 1)

  reduce m 0 0

end LinearAlgebra

/--
  Construct the verification matrix.
  Rows 1..3: from `active_L` (AQEI constraints).
  Rows 4..6: from Box constraints.

  Looking at coefficients:
  index 0: -1.07 (free)
  index 1: 100.0 (BOX ACTIVE)
  index 2: 100.0 (BOX ACTIVE)
  index 3: -0.73 (free)
  index 4: 0.49 (free)
  index 5: 100.0 (BOX ACTIVE)

  So we add rows for e_1, e_2, e_5 (0-indexed).
-/
def box_rows : Matrix := [
  [0.0, 1.0, 0.0, 0.0, 0.0, 0.0],
  [0.0, 0.0, 1.0, 0.0, 0.0, 0.0],
  [0.0, 0.0, 0.0, 0.0, 0.0, 1.0]
]

def verification_matrix : Matrix :=
  active_L ++ box_rows

def computed_rank : Nat := compute_rank verification_matrix

-- Verify rank is 6
#eval computed_rank

/--
  The formal statement (computationally verified).
  The active constraints form a full-rank system, isolating a single vertex.
-/
theorem active_constraints_full_rank : computed_rank = 6 := by
  rfl

end Phase2

-- Completeness checks
#print axioms Phase2.active_constraints_full_rank

