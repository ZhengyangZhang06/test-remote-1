import Submission.Obl.Entropy__mollified_convex_sequence.Convolution

open MeasureTheory Set Filter ContinuousLinearMap Metric
open scoped Topology Convolution

namespace Submission.Obl.Entropy__mollified_convex_sequence

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

lemma first_order_remainder_le {f : E → ℝ} (hf : Differentiable ℝ f)
    {L : ℝ} (hL : 0 ≤ L)
    (hl : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x-y‖)
    (x y : E) {r : ℝ} (hr : 0 ≤ r) (hy : ‖y-x‖ ≤ r) :
    ‖f y - f x - fderiv ℝ f x (y-x)‖ ≤ L * r ^ 2 := by
  have h := (convex_closedBall x r).norm_image_sub_le_of_norm_fderiv_le'
    (φ := fderiv ℝ f x) (C := L*r) (fun z _ => hf z)
    (fun z hz => (hl z x).trans (mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.mp hz) hL))
    (mem_closedBall_self hr) (mem_closedBall_iff_norm.mpr hy)
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hy (mul_nonneg hL hr)])

lemma integral_bump_linear (φ : ContDiffBump (0 : E)) (ℓ : E →L[ℝ] ℝ) :
    (∫ y, φ.normed volume y * ℓ y) = 0 := by
  have h := integral_neg_eq_self (fun y => φ.normed volume y * ℓ y) volume
  simp only [φ.normed_neg, map_neg, mul_neg, integral_neg] at h
  linarith

lemma smooth_error_le (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) {L : ℝ} (hL : 0 ≤ L)
    (hl : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x-y‖) (x : E) :
    ‖smooth φ f x - f x‖ ≤ L * φ.rOut ^ 2 := by
  have hiF : Integrable (fun y => φ.normed volume y * f (x-y)) :=
    bump_mul_integrable φ (hf.continuous.comp (continuous_const.sub continuous_id))
  have hiC : Integrable (fun y => φ.normed volume y * f x) := φ.integrable_normed.mul_const _
  have hiLin : Integrable (fun y => φ.normed volume y * fderiv ℝ f x y) :=
    bump_mul_integrable φ (fderiv ℝ f x).continuous
  have he : smooth φ f x - f x =
      ∫ y, φ.normed volume y * (f (x-y) - f x + fderiv ℝ f x y) := by
    simp_rw [mul_add, mul_sub]
    have hiFC : Integrable (fun y => φ.normed volume y * f (x-y) - φ.normed volume y * f x) :=
      hiF.sub hiC
    rw [integral_add hiFC hiLin, integral_sub hiF hiC,
      integral_mul_const, φ.integral_normed, integral_bump_linear, one_mul, add_zero,
      smooth_eq_integral]
  rw [he]
  calc
    _ ≤ ∫ y, φ.normed volume y * (L * φ.rOut ^ 2) := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _)
      apply Eventually.of_forall
      intro y
      by_cases hy : φ.normed volume y = 0
      · simp only [hy, zero_mul, norm_zero, le_refl]
      have hyr : ‖y‖ ≤ φ.rOut := by
        have hym : y ∈ Function.support (φ.normed volume) := hy
        rw [φ.support_normed_eq] at hym
        exact (mem_ball_zero_iff.mp hym).le
      have hd : (x-y)-x = -y := by abel
      have hrem := first_order_remainder_le (hf.differentiable one_ne_zero) hL hl x (x-y)
        φ.rOut_pos.le (show ‖(x-y)-x‖ ≤ φ.rOut by simpa [hd] using hyr)
      simp only [hd, map_neg, sub_neg_eq_add] at hrem
      rw [norm_mul, Real.norm_of_nonneg (φ.nonneg_normed y)]
      exact mul_le_mul_of_nonneg_left hrem (φ.nonneg_normed y)
    _ = L * φ.rOut ^ 2 := by rw [integral_mul_const, φ.integral_normed, one_mul]

end Submission.Obl.Entropy__mollified_convex_sequence
