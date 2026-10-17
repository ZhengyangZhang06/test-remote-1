import Submission.Obl.Entropy__transport_covariance_completion.WeakTesting

namespace Submission.Obl.Entropy__transport_covariance_completion

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution

set_option linter.unusedSectionVars false

variable {E r : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype r]
  {μ : Measure E} (ν : Measure E) [ν.IsAddHaarMeasure]

/-- The mollifiers shrink in both radii and have integral one after normalization. -/
noncomputable def weakMollifier (n : ℕ) : ContDiffBump (0 : E) where
  rIn := 1 / ((n : ℝ) + 1)
  rOut := 2 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := div_lt_div_of_pos_right one_lt_two (by positivity)

theorem weakMollifier_tendsto :
    Tendsto (fun n => (weakMollifier (E := E) n).rOut) atTop (𝓝 0) := by
  simpa only [weakMollifier, mul_zero, mul_one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2

theorem norm_normed_convolution_le (φ : ContDiffBump (0 : E)) {z : E → ℝ} {C : ℝ}
    (hC : ∀ x, ‖z x‖ ≤ C) (x : E) :
    ‖(φ.normed ν ⋆[lsmul ℝ ℝ, ν] z) x‖ ≤ C := by
  rw [convolution_def]
  calc
    _ ≤ ∫ t, φ.normed ν t * C ∂ν := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const C)
      filter_upwards [] with t
      simp only [lsmul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (φ.nonneg_normed t)]
      exact mul_le_mul_of_nonneg_left (hC _) (φ.nonneg_normed t)
    _ = C := by rw [integral_mul_const, φ.integral_normed, one_mul]

include ν in
/-- Mollification extends compact smooth testing to compact `C¹` testing. -/
theorem weak_testing_contDiff_one (e : r → E) {H z : E → ℝ} {v : r → E → ℝ}
    (hH : Integrable H μ) (hv : ∀ i, Integrable (v i) μ)
    (hweak : ∀ w : E → ℝ, ContDiff ℝ ∞ w → HasCompactSupport w →
      (∫ x, H x * w x ∂μ) = ∑ i, ∫ x, v i x * fderiv ℝ w x (e i) ∂μ)
    (hzs : ContDiff ℝ 1 z) (hzc : HasCompactSupport z) :
    (∫ x, H x * z x ∂μ) = ∑ i, ∫ x, v i x * fderiv ℝ z x (e i) ∂μ := by
  let φ (n : ℕ) := weakMollifier (E := E) n
  let w (n : ℕ) := (φ n).normed ν ⋆[lsmul ℝ ℝ, ν] z
  have hws n : ContDiff ℝ ∞ (w n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (φ n).contDiff_normed hzs.continuous.locallyIntegrable
  have hwc n : HasCompactSupport (w n) :=
    (φ n).hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hzc
  have hdzc (i : r) : Continuous (fun x => fderiv ℝ z x (e i)) :=
    (hzs.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hwder n x (i : r) : fderiv ℝ (w n) x (e i) =
      ((φ n).normed ν ⋆[lsmul ℝ ℝ, ν] fun y => fderiv ℝ z y (e i)) x := by
    rw [(hzc.hasFDerivAt_convolution_right (lsmul ℝ ℝ)
      (φ n).continuous_normed.locallyIntegrable hzs x).fderiv]
    exact convolution_precompR_apply (lsmul ℝ ℝ) (φ n).continuous_normed.locallyIntegrable
      (hzc.fderiv (𝕜 := ℝ)) (hzs.continuous_fderiv one_ne_zero) x (e i)
  obtain ⟨C, hC⟩ := hzc.exists_bound_of_continuous hzs.continuous
  have hleft : Tendsto (fun n => ∫ x, H x * w n x ∂μ) atTop
      (𝓝 (∫ x, H x * z x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖H x‖ * C)
    · exact fun n => hH.aestronglyMeasurable.mul (hws n).continuous.aestronglyMeasurable
    · exact hH.norm.mul_const C
    · intro n
      filter_upwards [] with x
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_normed_convolution_le ν (φ n) hC x) (norm_nonneg _)
    · filter_upwards [] with x
      exact tendsto_const_nhds.mul
        (ContDiffBump.convolution_tendsto_right_of_continuous
          weakMollifier_tendsto hzs.continuous x)
  have hright (i : r) : Tendsto (fun n => ∫ x, v i x * fderiv ℝ (w n) x (e i) ∂μ)
      atTop (𝓝 (∫ x, v i x * fderiv ℝ z x (e i) ∂μ)) := by
    obtain ⟨D, hD⟩ := (hzc.fderiv_apply (𝕜 := ℝ) (e i)).exists_bound_of_continuous (hdzc i)
    apply tendsto_integral_of_dominated_convergence (fun x => ‖v i x‖ * D)
    · exact fun n => (hv i).aestronglyMeasurable.mul
        (((hws n).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
    · exact (hv i).norm.mul_const D
    · intro n
      filter_upwards [] with x
      rw [norm_mul, hwder]
      exact mul_le_mul_of_nonneg_left (norm_normed_convolution_le ν (φ n) hD x) (norm_nonneg _)
    · filter_upwards [] with x
      simp only [hwder]
      exact tendsto_const_nhds.mul
        (ContDiffBump.convolution_tendsto_right_of_continuous
          weakMollifier_tendsto (hdzc i) x)
  have heq : (fun n => ∫ x, H x * w n x ∂μ) =
      (fun n => ∑ i, ∫ x, v i x * fderiv ℝ (w n) x (e i) ∂μ) :=
    funext (fun n => hweak (w n) (hws n) (hwc n))
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft (tendsto_finsetSum _ (fun i _ => hright i))

include ν in
/-- Compact smooth testing extends to every `C¹` Gaussian `H¹` test; more generally,
this holds for any finite Borel measure on a finite-dimensional real normed space. -/
theorem weak_h1_testing_contDiff_one [IsFiniteMeasure μ] (e : r → E)
    {H z : E → ℝ} {v : r → E → ℝ}
    (hH : MemLp H 2 μ) (hv : ∀ i, MemLp (v i) 2 μ)
    (hweak : ∀ w : E → ℝ, ContDiff ℝ ∞ w → HasCompactSupport w →
      (∫ x, H x * w x ∂μ) = ∑ i, ∫ x, v i x * fderiv ℝ w x (e i) ∂μ)
    (hzs : ContDiff ℝ 1 z) (hz : MemLp z 2 μ)
    (hdz : ∀ i, MemLp (fun x => fderiv ℝ z x (e i)) 2 μ) :
    (∫ x, H x * z x ∂μ) = ∑ i, ∫ x, v i x * fderiv ℝ z x (e i) ∂μ :=
  weak_h1_testing_of_contDiff 1 (by simp) e hH hv
    (fun w hws hwc => weak_testing_contDiff_one ν e (hH.integrable (by norm_num))
      (fun i => (hv i).integrable (by norm_num)) hweak hws hwc) hzs hz hdz

end Submission.Obl.Entropy__transport_covariance_completion
