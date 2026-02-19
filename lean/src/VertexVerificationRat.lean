import AQEI_Generated_Data_Rat

import Mathlib
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
    ((rows.getD i.val []).getD j.val 0)

section LinearAlgebra

abbrev RatRow := List Rat
abbrev RatMatrix := List RatRow

-- Subtract projection of pivot from row
-- row <- row - (row[col] / pivot[col]) * pivot
def eliminate (pivot : RatRow) (row : RatRow) (col_idx : Nat) : RatRow :=
  match pivot.get? col_idx, row.get? col_idx with
  | some p_val, some r_val =>
    if p_val == 0 then row
    else
      let factor := r_val / p_val
      List.zipWith (fun r p => r - factor * p) row pivot
  | _, _ => row

-- Exact Gaussian elimination to compute rank
partial def compute_rank (m : RatMatrix) : Nat :=
  let n_cols := match m.head? with | some r => r.length | none => 0

  let rec reduce (rows : RatMatrix) (c : Nat) (rank_acc : Nat) : Nat :=
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

/-
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

abbrev Vec6 := Fin 6 → Rat

def row0 : Vec6 := fun j =>
  match j.val with
  | 0 => (18242171 : Rat) / 185310433
  | 3 => (1686499 : Rat) / 783101748
  | _ => 0

def row1 : Vec6 := fun j =>
  match j.val with
  | 0 => (-61 : Rat) / 489973282
  | 2 => (-33857 : Rat) / 815586094
  | 3 => (-7864737 : Rat) / 141838453
  | 4 => (-110132019 : Rat) / 383795849
  | _ => 0

def row2 : Vec6 := fun j =>
  match j.val with
  | 0 => (-29649869 : Rat) / 504524770
  | 3 => (-188681736 : Rat) / 836755073
  | 4 => (-178 : Rat) / 269582495
  | 5 => (-320317 : Rat) / 94761543
  | _ => 0

def row3 : Vec6 := fun j => if j.val = 1 then 1 else 0
def row4 : Vec6 := fun j => if j.val = 2 then 1 else 0
def row5 : Vec6 := fun j => if j.val = 5 then 1 else 0

def verification_matrix : Matrix (Fin 6) (Fin 6) Rat :=
  fun i j =>
    match i.val with
    | 0 => row0 j
    | 1 => row1 j
    | 2 => row2 j
    | 3 => row3 j
    | 4 => row4 j
    | 5 => row5 j
    | _ => 0

-- Evaluate the determinant
def det_val : Rat := verification_matrix.det

theorem det_nonzero : det_val ≠ 0 := by native_decide

theorem full_rank_kernel_trivial :
    ∀ v : (Fin 6 → Rat), (Matrix.mulVec verification_matrix v = 0) → v = 0 := by
  intro v hv
  have h_det : verification_matrix.det ≠ 0 := det_nonzero
  have h_unit : IsUnit verification_matrix :=
    (Matrix.isUnit_iff_isUnit_det verification_matrix).mpr (isUnit_iff_ne_zero.mpr h_det)
  have h_inj : Function.Injective (Matrix.mulVec verification_matrix) :=
    Matrix.mulVec_injective_iff_isUnit.mpr h_unit
  have h0 : Matrix.mulVec verification_matrix 0 = 0 := Matrix.mulVec_zero _
  exact h_inj (hv.trans h0.symm)

end Phase2Rat

-- Completeness checks
#print axioms Phase2Rat.det_nonzero
#print axioms Phase2Rat.full_rank_kernel_trivial

/-- Cross-check: rows 0–2 of verification_matrix are consistent with active_L.
    Catches any transcription error between the two copies of the rational data.
    Proved by native_decide (exact rational evaluation). -/
theorem rows_match_active_L :
    (∀ j : Fin 6, Phase2Rat.row0 j = ((AQEIGeneratedRat.active_L.getD 0 []).getD j.val 0)) ∧
    (∀ j : Fin 6, Phase2Rat.row1 j = ((AQEIGeneratedRat.active_L.getD 1 []).getD j.val 0)) ∧
    (∀ j : Fin 6, Phase2Rat.row2 j = ((AQEIGeneratedRat.active_L.getD 2 []).getD j.val 0)) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro j <;> fin_cases j <;> native_decide

#print axioms rows_match_active_L
