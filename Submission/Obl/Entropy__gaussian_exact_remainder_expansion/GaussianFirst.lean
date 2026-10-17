import Submission.Obl.Entropy__gaussian_exact_remainder_expansion.Pointwise
import Submission.Obl.Entropy__gaussian_first_chaos_h1_projection.Analytic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped BigOperators

namespace Submission.Obl.Entropy__gaussian_exact_remainder_expansion

lemma integral_trace_left_zero {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} {Q : α → Matrix ι ι ℝ} (hQ : MatrixLp μ 1 Q)
    (hz : ∀ i j, ∫ x, Q x i j ∂μ = 0) (P : Matrix ι ι ℝ) :
    (∫ x, (P*Q x).trace ∂μ) = 0 := by
  have hi (i j) : Integrable (fun x => P i j*Q x j i) μ :=
    (memLp_one_iff_integrable.mp (hQ j i)).const_mul _
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j), integral_const_mul, hz,
    mul_zero, Finset.sum_const_zero]

lemma defect₁_zero {m : ℕ} {A : E m → Mat m} (hr : FCRegular A) :
    (∫ x, defect₁ A x ∂γ m) = 0 := by
  let Q (r : Fin m) (x : E m) : Mat m := x r • c A f x-d (c A f) r x
  have hq (r : Fin m) : MatrixLp (γ m) 1 (Q r) := by
    intro i j
    have hprod : MemLp (fun x : E m => x r*c A f x i j) 1 (γ m) :=
      (hr.lp smooth_f 2 i j).mul
        (Submission.Obl.Entropy__gaussian_first_chaos_h1_projection.coord_memLp r)
    exact hprod.sub (((hr f smooth_f).2.2 r i j).mono_exponent (by norm_num))
  have hz (r i j : Fin m) : (∫ x, Q r x i j ∂γ m) = 0 := by
    change (∫ x, x r*c A f x i j-d (c A f) r x i j ∂γ m) = 0
    have hi : Integrable (fun x : E m => x r*c A f x i j) (γ m) := (Submission.Obl.Entropy__gaussian_first_chaos_h1_projection.coord_memLp r).integrable_mul
      (hr.lp smooth_f 2 i j)
    erw [integral_sub hi (((hr f smooth_f).2.2 r).integrable i j), sub_eq_zero]
    exact (Submission.Obl.Entropy__gaussian_first_chaos_h1_projection.gaussian_integral_fderiv_of_memLp
      (((hr f smooth_f).1 i j).differentiable (by norm_num)) (hr.lp smooth_f 2 i j) r
      ((hr f smooth_f).2.2 r i j)).symm
  have he (x : E m) : defect₁ A x = ∑ r, (T A*X A r*Q r x).trace := by
    unfold defect₁
    have hfield : (A x-Y A x)*c A f x-(∑ r, X A r*d (c A f) r x) =
        ∑ r, X A r*Q r x := by
      simp only [Y, sub_sub_cancel, Matrix.sum_mul, Matrix.smul_mul, Q,
        Matrix.mul_sub, Matrix.mul_smul, Finset.sum_sub_distrib]
    rw [hfield]
    simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
  rw [funext he]
  rw [integral_finsetSum _ (fun r _ => ((hq r).const_mul (T A*X A r)).integrable_trace)]
  simp only [integral_trace_left_zero (hq _) (hz _), Finset.sum_const_zero]

end Submission.Obl.Entropy__gaussian_exact_remainder_expansion
