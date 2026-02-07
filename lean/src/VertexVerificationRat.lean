import AQEI_Generated_Data_Rat

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import ExtremeRays
import PolyhedralVertex

namespace Phase2Rat

open AQEIGeneratedRat

/--
  VertexVerificationRat.lean

  Formal verification of the vertex property using Exact Rational Arithmetic.
-/

-- Convert lists to Matrix
def listToMatrix (rows : List (List Rat)) : Matrix (Fin 6) (Fin 6) Rat :=
  fun i j =>
    match rows.get? i with
    | some row =>
      match row.get? j with
      | some val => val
      | none => 0
    | none => 0

section LinearAlgebra

abbrev Row := List Rat
abbrev Matrix := List Row

-- Subtract projection of pivot from row
-- row <- row - (row[col] / pivot[col]) * pivot
def eliminate (pivot : Row) (row : Row) (col_idx : Nat) : Row :=
  match pivot.get? col_idx, row.get? col_idx with
  | some p_val, some r_val =>
    if p_val == 0 then row
    else
      let factor := r_val / p_val
      List.zipWith (fun r p => r - factor * p) row pivot
  | _, _ => row

-- Exact Gaussian elimination to compute rank
def compute_rank (m : Matrix) : Nat :=
  let n_rows := m.length
  let n_cols := match m.head? with | some r => r.length | none => 0

  let rec reduce (rows : Matrix) (c : Nat) (rank_acc : Nat) : Nat :=
    if c >= n_cols || rows.isEmpty then rank_acc
    else
      -- Find pivot in current column `c` (First non-zero)
      let pivot_idx_opt := rows.findIdx? (fun r => match r.get? c with | some v => v != 0 | none => false)

      match pivot_idx_opt with
      | none =>
        -- No pivot in this column, move to next
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
  The Rational verification matrix.
  Rows 1..3: from `active_L` (AQEI constraints).
  Rows 4..6: from Box constraints.

  Indices (0-based) for Box Constraints from previous analysis:
  x1 (idx 1), x2 (idx 2), x5 (idx 5) were active at 100.
-/
def box_rows_list : List (List Rat) := [
  [0, 1, 0, 0, 0, 0],
  [0, 0, 1, 0, 0, 0],
  [0, 0, 0, 0, 0, 1]
]

def verification_rows : List (List Rat) :=
  active_L ++ box_rows_list

def verification_matrix : Matrix (Fin 6) (Fin 6) Rat :=
  listToMatrix verification_rows

-- Evaluate the determinant
def det_val : Rat := verification_matrix.det

#eval det_val

theorem det_nonzero : det_val ≠ 0 := by
  -- We trust the #eval for the value.
  -- In a fully rigorous proof without 'native_decide', we would need to provide the calculation step-by-step or use 'norm_num'.
  -- Given the size, norm_num might be slow but let's assume native_decide is acceptable for this "Computational Verification".
  native_decide

theorem full_rank_kernel_trivial :
    ∀ v : (Fin 6 → Rat), (verification_matrix *ᵥ v = 0) → v = 0 := by
  have h_det : verification_matrix.det ≠ 0 := det_nonzero
  have h_unit : IsUnit verification_matrix := Matrix.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr h_det)
  exact Matrix.isUnit_iff_isUnit_det.mp (Matrix.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr h_det)) |>.mulVec_eq_zero_iff_eq_zero.mp
