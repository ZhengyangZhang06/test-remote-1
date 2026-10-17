/-
Adapted from: here:root
Original matrix inequality proofs by session x0024.
-/

import Mathlib

/-!
# The supporting-plane inequality for the log determinant

This is the matrix logarithm estimate used at the start of Section 3's
entropy deficit reduction. No commutation of the two positive matrices is needed.
-/

open scoped BigOperators MatrixOrder

namespace Submission.Lib.MatrixEntropy

/-- The scalar logarithm supporting line summed over the positive eigenvalues. -/
theorem log_det_le_trace_sub_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    Real.log A.det ≤ A.trace - Fintype.card ι := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  change Real.log (∏ i, hA.isHermitian.eigenvalues i) ≤ A.trace - Fintype.card ι
  rw [Real.log_prod (fun i _ => (hA.eigenvalues_pos i).ne'),
    hA.isHermitian.trace_eq_sum_eigenvalues]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i))
  simpa [Finset.sum_sub_distrib] using h

/-- The log determinant lies below the supporting plane with positive matrix weight `S`. -/
theorem log_det_supporting_plane {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C S : Matrix ι ι ℝ} (hC : C.PosDef) (hS : S.PosDef) :
    Real.log C.det + Fintype.card ι ≤ (S * C).trace - Real.log S.det := by
  let R := CFC.sqrt S
  have hR : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)
  have hu : IsUnit R := (CFC.isUnit_sqrt_iff S hS.posSemidef.nonneg).2 hS.isUnit
  have hRR : R * R = S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hB : (R * C * R).PosDef := by
    simpa only [Matrix.star_eq_conjTranspose, hR.isHermitian.eq] using
      (Matrix.IsUnit.posDef_star_right_conjugate_iff hu).2 hC
  have ht : (R * C * R).trace = (S * C).trace := by
    rw [Matrix.trace_mul_cycle, hRR]
  have hd : (R * C * R).det = S.det * C.det := by
    rw [← hRR]
    simp only [Matrix.det_mul]
    ring
  have hb := log_det_le_trace_sub_card hB
  rw [ht, hd, Real.log_mul hS.det_pos.ne' hC.det_pos.ne'] at hb
  linarith

end Submission.Lib.MatrixEntropy
