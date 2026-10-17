import Submission.Obl.Entropy__smooth_gaussian_transport.GaussianKernel

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace Convolution NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Compact support of the integrable factor suffices for smooth convolution
with a smooth kernel that is not compactly supported. -/
theorem compact_convolution_contDiff {m : ℕ} {f g : E m → ℝ}
    (hf : LocallyIntegrable f volume) (hfc : HasCompactSupport f)
    {n : ENat} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := by
  obtain ⟨R, hR, hb⟩ := hfc.isBounded.exists_pos_norm_le
  apply contDiff_iff_contDiffAt.mpr
  intro c
  let κ : ContDiffBump (0 : E m) := ⟨R + ‖c‖ + 2, R + ‖c‖ + 3, by positivity, by linarith⟩
  let k : E m → ℝ := fun y => κ y * g y
  have hk : HasCompactSupport k := κ.hasCompactSupport.mul_right
  have hks : ContDiff ℝ n k := κ.contDiff.mul hg
  have hs := (hk.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hf hks).contDiffAt (x := c)
  apply hs.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds c (by norm_num : (0 : ℝ) < 1)] with x hx
  apply integral_congr_ae
  filter_upwards [] with y
  change f y * g (x - y) = f y * k (x - y)
  by_cases hy : f y = 0
  · simp only [hy, zero_mul]
  have hys : y ∈ tsupport f := subset_closure hy
  have hyn := hb y hys
  have hxb : ‖x - y‖ ≤ κ.rIn := by
    have hxc : ‖x - c‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have htri : ‖x - y‖ ≤ ‖x - c‖ + ‖c‖ + ‖y‖ := by
      calc
        _ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ (‖x - c‖ + ‖c‖) + ‖y‖ := by
          gcongr
          simpa only [sub_add_cancel] using norm_add_le (x - c) c
    dsimp only [κ]
    linarith
  have hκ : κ (x - y) = 1 := κ.one_of_mem_closedBall (by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hxb)
  simp only [k, hκ, one_mul]

noncomputable def gaussianSmoothing {m : ℕ} (r : ℝ) (f : E m → ℝ) : E m → ℝ :=
  f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] gaussianKernel r

theorem gaussianSmoothing_contDiff {m : ℕ} (r : ℝ) {f : E m → ℝ}
    (hf : LocallyIntegrable f volume) (hfc : HasCompactSupport f) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (gaussianSmoothing r f) :=
  compact_convolution_contDiff hf hfc (gaussianKernel_contDiff r)

/-- Positive-scale Gaussian convolution is an approximate identity. -/
theorem gaussianSmoothing_tendsto {m : ℕ} {f : E m → ℝ} (hf : Integrable f volume)
    {x : E m} (hfx : ContinuousAt f x) :
    Tendsto (fun c : ℝ => gaussianSmoothing c⁻¹ f x) atTop (𝓝 (f x)) := by
  have hdecay : Tendsto (fun y : E m => ‖y‖ ^ Module.finrank ℝ (E m) *
      Submission.Lib.EntropyRemainder.gaussianDensity y) (Bornology.cobounded (E m)) (𝓝 0) := by
    have ht : Tendsto (fun r : ℝ => r ^ m * Real.exp (-(1 / 2 : ℝ) * r ^ 2)) atTop (𝓝 0) := by
      simpa only [Real.rpow_natCast] using
        (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg (by norm_num : (0 : ℝ) < 1 / 2) (m : ℝ)).tendsto_zero_of_tendsto
          (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(1 / 2 : ℝ) < 0)))
    have hnorm : Tendsto (fun y : E m => ‖y‖) (Bornology.cobounded (E m)) atTop :=
      tendsto_norm_cobounded_atTop
    have hh := (ht.comp hnorm).mul_const ((Real.sqrt (2 * Real.pi))⁻¹ ^ m)
    convert! hh using 1
    · ext y
      simp only [E, finrank_euclideanSpace_fin, Submission.Lib.EntropyRemainder.gaussianDensity,
        Function.comp_apply]
      have he : -(‖y‖ ^ 2) / 2 = -(1 / 2 : ℝ) * ‖y‖ ^ 2 := by ring
      rw [he]
      ring
    · simp
  have hh := tendsto_integral_comp_smul_smul_of_integrable'
    (μ := (volume : Measure (E m)))
    (fun y => (Submission.Lib.EntropyRemainder.gaussianDensity_pos y).le)
    gaussianDensity_integral hdecay hf hfx
  convert! hh using 1
  ext c
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [gaussianSmoothing, convolution_def, gaussianKernel, inv_pow, inv_inv,
    E, finrank_euclideanSpace_fin, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  ring

end Submission.Obl.Entropy__smooth_gaussian_transport
