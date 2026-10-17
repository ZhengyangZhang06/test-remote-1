import Submission.Obl.Entropy__mollified_convex_sequence.Convolution

open MeasureTheory Set Filter ContinuousLinearMap Metric
open scoped Topology Convolution

set_option maxHeartbeats 400000

namespace Submission.Obl.Entropy__mollified_convex_sequence

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

lemma smooth_hasFDerivAt (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) {L : ℝ} (hL : 0 ≤ L)
    (hl : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x-y‖) (x₀ : E) :
    HasFDerivAt (smooth φ f) (∫ y, φ.normed volume y • fderiv ℝ f (x₀-y)) x₀ := by
  have hd := hf.differentiable one_ne_zero
  have hc := hf.continuous_fderiv one_ne_zero
  change HasFDerivAt (fun x => ∫ y, φ.normed volume y * f (x-y)) _ x₀
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := ball x₀ 1)
    (F' := fun x y => φ.normed volume y • fderiv ℝ f (x-y))
    (bound := fun y => φ.normed volume y * (‖fderiv ℝ f x₀‖ + L * (1+φ.rOut)))
    (ball_mem_nhds x₀ zero_lt_one)
  · exact Eventually.of_forall fun x =>
      (bump_mul_integrable φ (hf.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · exact bump_mul_integrable φ (hf.continuous.comp (continuous_const.sub continuous_id))
  · exact (bump_smul_integrable φ (hc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · apply Eventually.of_forall
    intro y x hx
    by_cases hy : φ.normed volume y = 0
    · simp only [hy, zero_smul, norm_zero, zero_mul, le_refl]
    have hyr : ‖y‖ ≤ φ.rOut := by
      have hym : y ∈ Function.support (φ.normed volume) := hy
      rw [φ.support_normed_eq] at hym
      exact (mem_ball_zero_iff.mp hym).le
    have hxy : ‖(x-y)-x₀‖ ≤ 1+φ.rOut := by
      calc
        ‖(x-y)-x₀‖ = ‖(x-x₀)-y‖ := by congr 1; abel
        _ ≤ ‖x-x₀‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ 1+φ.rOut := add_le_add (mem_ball_iff_norm.mp hx).le hyr
    have hnorm : ‖fderiv ℝ f (x-y)‖ ≤ ‖fderiv ℝ f x₀‖ + L * (1+φ.rOut) := by
      calc
        ‖fderiv ℝ f (x-y)‖ ≤ ‖fderiv ℝ f (x-y) - fderiv ℝ f x₀‖ + ‖fderiv ℝ f x₀‖ :=
          by simpa only [norm_sub_rev, add_comm] using
            norm_le_insert (fderiv ℝ f x₀) (fderiv ℝ f (x-y))
        _ ≤ L * ‖(x-y)-x₀‖ + ‖fderiv ℝ f x₀‖ := by
          simpa only [add_comm] using
            (_root_.add_le_add_right (hl (x-y) x₀) ‖fderiv ℝ f x₀‖)
        _ ≤ ‖fderiv ℝ f x₀‖ + L * (1+φ.rOut) := by
          simpa only [add_comm] using
            add_le_add_right (mul_le_mul_of_nonneg_left hxy hL) ‖fderiv ℝ f x₀‖
    rw [norm_smul, Real.norm_of_nonneg (φ.nonneg_normed y)]
    exact mul_le_mul_of_nonneg_left hnorm (φ.nonneg_normed y)
  · exact φ.integrable_normed.mul_const _
  · apply Eventually.of_forall
    intro y x hx
    have h := ((hd (x-y)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub (hasFDerivAt_const y x))).const_smul (φ.normed volume y)
    simpa [Function.comp_def, Pi.smul_def, Pi.sub_apply, smul_eq_mul] using h

lemma smooth_fderiv (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) {L : ℝ} (hL : 0 ≤ L)
    (hl : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x-y‖) (x : E) :
    fderiv ℝ (smooth φ f) x = ∫ y, φ.normed volume y • fderiv ℝ f (x-y) :=
  (smooth_hasFDerivAt φ hf hL hl x).fderiv

lemma smooth_fderiv_lipschitz (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) {L : ℝ} (hL : 0 ≤ L)
    (hl : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x-y‖) (x z : E) :
    ‖fderiv ℝ (smooth φ f) x - fderiv ℝ (smooth φ f) z‖ ≤ L * ‖x-z‖ := by
  rw [smooth_fderiv φ hf hL hl, smooth_fderiv φ hf hL hl]
  have hc := hf.continuous_fderiv one_ne_zero
  have hi (u : E) : Integrable (fun y => φ.normed volume y • fderiv ℝ f (u-y)) :=
    bump_smul_integrable φ (hc.comp (continuous_const.sub continuous_id))
  rw [← integral_sub (hi x) (hi z)]
  calc
    _ ≤ ∫ y, φ.normed volume y * (L * ‖x-z‖) := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _)
      apply Eventually.of_forall
      intro y
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (φ.nonneg_normed y)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed y)
      simpa only [sub_sub_sub_cancel_right] using hl (x-y) (z-y)
    _ = L * ‖x-z‖ := by rw [integral_mul_const, φ.integral_normed, one_mul]

end Submission.Obl.Entropy__mollified_convex_sequence
