import Mathlib

open MeasureTheory Set Filter ContinuousLinearMap Metric
open scoped Topology Convolution

namespace Submission.Obl.Entropy__mollified_convex_sequence

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

noncomputable def smooth (φ : ContDiffBump (0 : E)) (f : E → ℝ) : E → ℝ :=
  φ.normed volume ⋆ f

lemma smooth_contDiff (φ : ContDiffBump (0 : E)) {f : E → ℝ} (hf : Continuous f) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (smooth φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    φ.contDiff_normed hf.locallyIntegrable

lemma bump_mul_integrable (φ : ContDiffBump (0 : E)) {g : E → ℝ}
    (hg : Continuous g) : Integrable (fun y => φ.normed volume y * g y) :=
  (φ.continuous_normed.mul hg).integrable_of_hasCompactSupport
    φ.hasCompactSupport_normed.mul_right

lemma bump_smul_integrable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : ContDiffBump (0 : E)) {g : E → F} (hg : Continuous g) :
    Integrable (fun y => φ.normed volume y • g y) :=
  (φ.continuous_normed.smul hg).integrable_of_hasCompactSupport
    φ.hasCompactSupport_normed.smul_right

lemma smooth_eq_integral (φ : ContDiffBump (0 : E)) (f : E → ℝ) (x : E) :
    smooth φ f x = ∫ y, φ.normed volume y * f (x - y) := rfl

lemma smooth_eq_integral_add (φ : ContDiffBump (0 : E)) (f : E → ℝ) (x : E) :
    smooth φ f x = ∫ y, φ.normed volume y * f (x + y) := by
  rw [smooth_eq_integral, ← integral_neg_eq_self (fun y => φ.normed volume y * f (x - y))]
  simp only [φ.normed_neg, sub_neg_eq_add]

lemma smooth_convex (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : Continuous f) (hc : ConvexOn ℝ univ f) : ConvexOn ℝ univ (smooth φ f) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ a b ha hb hab
  simp only [smooth_eq_integral, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
  · apply integral_mono
    · exact bump_mul_integrable φ (hf.comp (continuous_const.sub continuous_id))
    · exact ((bump_mul_integrable φ (hf.comp (continuous_const.sub continuous_id))).const_mul a).add
        ((bump_mul_integrable φ (hf.comp (continuous_const.sub continuous_id))).const_mul b)
    · intro y
      have he : a • x + b • z - y = a • (x - y) + b • (z - y) := by
        calc
          a • x + b • z - y = a • x + b • z - (a+b) • y := by rw [hab, one_smul]
          _ = a • (x-y) + b • (z-y) := by module
      dsimp only
      rw [he]
      have hi := hc.2 (mem_univ (x-y)) (mem_univ (z-y)) ha hb hab
      have := mul_le_mul_of_nonneg_left hi (φ.nonneg_normed y (μ := volume))
      dsimp at this
      simpa only [smul_eq_mul] using this.trans_eq (by ring)
  · exact (bump_mul_integrable φ (hf.comp (continuous_const.sub continuous_id))).const_mul a
  · exact (bump_mul_integrable φ (hf.comp (continuous_const.sub continuous_id))).const_mul b

lemma le_smooth (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : Continuous f) (hc : ConvexOn ℝ univ f) (x : E) : f x ≤ smooth φ f x := by
  have hi1 : Integrable (fun y => φ.normed volume y * f (x-y)) :=
    bump_mul_integrable φ (hf.comp (continuous_const.sub continuous_id))
  have hi2 : Integrable (fun y => φ.normed volume y * f (x+y)) :=
    bump_mul_integrable φ (hf.comp (continuous_const.add continuous_id))
  have he : (∫ y, φ.normed volume y * (f (x-y) + f (x+y))) = 2 * smooth φ f x := by
    simp_rw [mul_add]
    rw [integral_add hi1 hi2, ← smooth_eq_integral, ← smooth_eq_integral_add]
    ring
  have h := integral_mono (φ.integrable_normed.mul_const (2 * f x)) (hi1.add hi2) (fun y => ?_)
  · simp only [integral_mul_const, φ.integral_normed, one_mul] at h
    have he' : (∫ y, (φ.normed volume y * f (x-y) + φ.normed volume y * f (x+y))) =
        2 * smooth φ f x := by simpa only [mul_add] using he
    dsimp only [Pi.add_apply] at h
    rw [he'] at h
    linarith
  · have hx : (1 / 2 : ℝ) • (x-y) + (1 / 2 : ℝ) • (x+y) = x := by module
    have hh := hc.2 (mem_univ (x-y)) (mem_univ (x+y))
      (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num)
      (show (1/2 : ℝ) + 1/2 = 1 by norm_num)
    rw [hx] at hh
    simp only [smul_eq_mul] at hh
    have := mul_le_mul_of_nonneg_left (show 2 * f x ≤ f (x-y) + f (x+y) by linarith)
      (φ.nonneg_normed y (μ := volume))
    simpa only [Pi.add_apply, mul_add] using this

end Submission.Obl.Entropy__mollified_convex_sequence
