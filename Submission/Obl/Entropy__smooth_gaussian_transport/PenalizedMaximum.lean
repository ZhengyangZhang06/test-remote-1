import Submission.Obl.Entropy__smooth_gaussian_transport.GradientGrowth
import Submission.Obl.Entropy__smooth_gaussian_transport.ScaledTilt

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem symmetricAverage_sub_linear_growth {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hd : Differentiable ℝ u) {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ x, ‖gradient u x‖ ≤ C * (1 + ‖x‖)) (h x : E m) :
    symmetricAverage u h x - u x ≤ C * ‖h‖ * ‖x‖ + C * ‖h‖ * (1 + ‖h‖) := by
  have hdiff := symmetricAverage_sub_le_gradient_difference hu hd h x
  have hnorm := norm_sub_le (gradient u (x + h)) (gradient u (x - h))
  have hp := hg (x + h)
  have hn := hg (x - h)
  have hpx := mul_le_mul_of_nonneg_left (norm_add_le x h) hC
  have hnx := mul_le_mul_of_nonneg_left (norm_sub_le x h) hC
  have hsum : ‖gradient u (x + h) - gradient u (x - h)‖ ≤
      2 * C * (1 + ‖x‖ + ‖h‖) := by linarith
  have hh := mul_le_mul_of_nonneg_right hsum (norm_nonneg h)
  nlinarith only [hdiff, hh]

/-- A positive multiple of a superlinear potential makes the centered
second-difference maximum attainable. -/
theorem exists_max_penalized_symmetricAverage {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hC1 : ContDiff ℝ 1 u) (hdom : conjugateDomain u = univ)
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ x, ‖gradient u x‖ ≤ C * (1 + ‖x‖))
    (p h : E m) {c : ℝ} (hc : 1 < c) :
    ∃ z, ∀ x, symmetricAverage u h x - scaledTilt u p c x ≤
      symmetricAverage u h z - scaledTilt u p c z := by
  obtain ⟨C, hC, hg⟩ := hgrowth
  let A := C * ‖h‖
  let B := C * ‖h‖ * (1 + ‖h‖)
  let ε := c - 1
  have hε : 0 < ε := sub_pos.mpr hc
  have hR : 0 ≤ (A + 1) / ε := by dsimp [A]; positivity
  obtain ⟨M, hM⟩ := arbitrary_linear_minorant (tilt_conjugateDomain hdom p 0) hR
  have hbound (x : E m) :
      symmetricAverage u h x - scaledTilt u p c x ≤ -‖x‖ + (B + ε * M) := by
    have h₁ := symmetricAverage_sub_linear_growth hu hC1.differentiable_one hC.le hg h x
    change symmetricAverage u h x - u x ≤ A * ‖x‖ + B at h₁
    have h₂ := mul_le_mul_of_nonneg_left (hM x) hε.le
    have he : ε * ((A + 1) / ε * ‖x‖ - M) = (A + 1) * ‖x‖ - ε * M := by
      field_simp
    rw [he] at h₂
    simp only [tilt, sub_zero] at h₂
    dsimp only [scaledTilt, ε] at *
    nlinarith only [h₁, h₂]
  have ht : Tendsto (fun x : E m => -‖x‖ + (B + ε * M)) (cocompact (E m)) atBot :=
    tendsto_atBot_add_const_right _ _ (tendsto_neg_atTop_atBot.comp tendsto_norm_cocompact_atTop)
  exact ((symmetricAverage_contDiff hC1 h).continuous.sub
    (scaledTilt_contDiff hC1 p c).continuous).exists_forall_ge (tendsto_atBot_mono hbound ht)

end Submission.Obl.Entropy__smooth_gaussian_transport
