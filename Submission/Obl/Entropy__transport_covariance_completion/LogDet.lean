import Mathlib

namespace Submission.Obl.Entropy__transport_covariance_completion

open Matrix
open scoped BigOperators MatrixOrder

/-- The scalar logarithm bound, summed over the positive eigenvalues. -/
theorem log_det_le_trace_sub_card {n : Type*} [Fintype n] [DecidableEq n]
    {C : Matrix n n ℝ} (hC : C.PosDef) :
    Real.log C.det ≤ C.trace - Fintype.card n := by
  rw [hC.isHermitian.det_eq_prod_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [Real.log_prod (fun i _ => ne_of_gt (hC.eigenvalues_pos i)),
    hC.isHermitian.trace_eq_sum_eigenvalues]
  simpa only [RCLike.ofReal_real_eq_id, id_eq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] using Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => Real.log_le_sub_one_of_pos (hC.eigenvalues_pos i))

/-- A supporting plane for the log determinant, with an arbitrary positive definite weight. -/
theorem log_det_supporting_plane {n : Type*} [Fintype n] [DecidableEq n]
    {C P : Matrix n n ℝ} (hC : C.PosDef) (hP : P.PosDef) :
    Real.log C.det + Fintype.card n ≤ (P * C).trace - Real.log P.det := by
  let Q := CFC.sqrt P
  have hQsq : Q * Q = P := CFC.sqrt_mul_sqrt_self P hP.posSemidef.nonneg
  have hQherm : Q.IsHermitian := (CFC.sqrt_nonneg P).posSemidef.isHermitian
  have hQunit : IsUnit Q := (CFC.isUnit_sqrt_iff P hP.posSemidef.nonneg).mpr hP.isUnit
  have hQCQ : (Q * C * Q).PosDef := by
    simpa only [star_eq_conjTranspose, hQherm.eq] using
      hQunit.posDef_star_left_conjugate_iff.mpr hC
  have htrace : (Q * C * Q).trace = (P * C).trace := by
    rw [trace_mul_cycle, hQsq]
  have hdet : (Q * C * Q).det = P.det * C.det := by
    calc
      (Q * C * Q).det = (Q * Q).det * C.det := by simp only [det_mul]; ring
      _ = P.det * C.det := by rw [hQsq]
  have h := log_det_le_trace_sub_card hQCQ
  rw [htrace, hdet, Real.log_mul (ne_of_gt hP.det_pos) (ne_of_gt hC.det_pos)] at h
  linarith

end Submission.Obl.Entropy__transport_covariance_completion
