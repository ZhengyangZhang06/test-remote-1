/-
Adapted from: here:root
Original matrix inequality proofs by session x0024.
-/

import Mathlib

/-!
# Weighted matrix squares

The block Cauchy--Schwarz estimate from Section 3, expressed through finite
families of rectangular matrices. The proof keeps all multiplication orders.
-/

open scoped BigOperators

namespace Submission.Lib.MatrixEntropy

lemma trace_transpose_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A B : Matrix ι κ ℝ) :
    (A.transpose * B).trace = ∑ i, ∑ j, A i j * B i j := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- Young's inequality for the Frobenius pairing of two rectangular matrices. -/
theorem matrix_trace_young {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A B : Matrix ι κ ℝ) {s : ℝ} (hs : 0 < s) :
    2 * (A.transpose * B).trace ≤
      s * (A.transpose * A).trace + s⁻¹ * (B.transpose * B).trace := by
  simp only [trace_transpose_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h : 0 ≤ (s * A i j - B i j) ^ 2 / s := div_nonneg (sq_nonneg _) hs.le
  have heq : (s * A i j - B i j) ^ 2 / s =
      s * (A i j * A i j) + s⁻¹ * (B i j * B i j) - 2 * (A i j * B i j) := by
    field_simp
    ring
  rw [heq] at h
  linarith

/-- Finite block Cauchy--Schwarz, using a weighted right inverse of the row operator. -/
theorem matrix_block_bound {ρ ι κ ν : Type*} [Fintype ρ] [Fintype ι]
    [Fintype κ] [Fintype ν]
    (X : ρ → Matrix ι κ ℝ) (L : ρ → Matrix κ ν ℝ)
    (w : ρ → ℝ) (hw : ∀ r, 0 < w r) (S : Matrix ι ι ℝ)
    (hS : S.IsHermitian)
    (hinv : S * (∑ r, (w r)⁻¹ • (X r * (X r).transpose)) * S = S) :
    let F := ∑ r, X r * L r
    (F.transpose * S * F).trace ≤ ∑ r, w r * ((L r).transpose * L r).trace := by
  classical
  intro F
  have hsym : S.transpose = S := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hS
  have h := Finset.sum_le_sum (s := Finset.univ) fun r _ =>
    matrix_trace_young (L r) ((X r).transpose * S * F) (hw r)
  have hleft : (∑ r, 2 * ((L r).transpose * ((X r).transpose * S * F)).trace) =
      2 * (F.transpose * S * F).trace := by
    dsimp [F]
    simp only [Matrix.transpose_sum, Matrix.transpose_mul, Matrix.sum_mul,
      Matrix.trace_sum, Finset.mul_sum, Matrix.mul_assoc]
  have hright : (∑ r, (w r)⁻¹ *
      (((X r).transpose * S * F).transpose * ((X r).transpose * S * F)).trace) =
        (F.transpose * S * F).trace := by
    calc
      _ = (F.transpose * (S * (∑ r, (w r)⁻¹ •
            (X r * (X r).transpose)) * S) * F).trace := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hsym,
          Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
      _ = _ := by rw [hinv]
  rw [hleft, Finset.sum_add_distrib, hright] at h
  linarith

/-- The block estimate in the form used in Section 3, equation (3.22). -/
theorem matrix_block_bound_add {ρ ι ν : Type*} [Fintype ρ] [Fintype ι]
    [Fintype ν] [DecidableEq ι]
    (X : ρ → Matrix ι ι ℝ) (L : ρ → Matrix ι ν ℝ) (a : Matrix ι ν ℝ)
    {s α : ℝ} (hs : 0 < s) (hα : 0 < α) (S : Matrix ι ι ℝ)
    (hS : S.PosDef)
    (hinv : S⁻¹ = s⁻¹ • (1 : Matrix ι ι ℝ) +
      α • ∑ r, X r * (X r).transpose) :
    let F := a + ∑ r, X r * L r
    (F.transpose * S * F).trace ≤
      s * (a.transpose * a).trace + α⁻¹ * ∑ r, ((L r).transpose * L r).trace := by
  classical
  let X' : Option ρ → Matrix ι ι ℝ := Option.elim' 1 X
  let L' : Option ρ → Matrix ι ν ℝ := Option.elim' a L
  let w : Option ρ → ℝ := Option.elim' s (fun _ => α⁻¹)
  have hw : ∀ r, 0 < w r := by
    intro r
    cases r with
    | none => exact hs
    | some r => exact inv_pos.2 hα
  have hsum : (∑ r, (w r)⁻¹ • (X' r * (X' r).transpose)) = S⁻¹ := by
    simp [X', w, Fintype.sum_option, hinv, Finset.smul_sum]
  have hi : S * (∑ r, (w r)⁻¹ • (X' r * (X' r).transpose)) * S = S := by
    rw [hsum, Matrix.mul_nonsing_inv S (Matrix.isUnit_iff_isUnit_det S |>.1 hS.isUnit),
      one_mul]
  have h := matrix_block_bound X' L' w hw S hS.isHermitian hi
  simpa [X', L', w, Fintype.sum_option, Finset.mul_sum, add_comm] using h

end Submission.Lib.MatrixEntropy
