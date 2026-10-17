import Submission.Obl.Entropy__smooth_gaussian_transport.GaussianHeat
import Submission.Obl.Entropy__smooth_gaussian_transport.GaussianSmoothingEstimates

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace Convolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Joint kernel continuity gives scale continuity of each smoothing derivative. -/
theorem gaussianSmoothing_derivative_scale_continuous {m : ℕ} {f : E m → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (n : ℕ) (x : E m) :
    ContinuousOn (fun r : ℝ => iteratedFDeriv ℝ n (gaussianSmoothing r f) x) (Ioi 0) := by
  have hp : Continuous (fun z : ℝ × E m => (z.1, x - z.2)) :=
    continuous_fst.prodMk (continuous_const.sub continuous_snd)
  have hmap : MapsTo (fun z : ℝ × E m => (z.1, x - z.2))
      (Ioi 0 ×ˢ univ) (Ioi 0 ×ˢ univ) := fun z hz => ⟨hz.1, mem_univ _⟩
  have hc : ContinuousOn (fun z : ℝ × E m =>
      f z.2 • iteratedFDeriv ℝ n (gaussianKernel z.1) (x - z.2)) (Ioi 0 ×ˢ univ) :=
    (hf.comp continuous_snd).continuousOn.smul
      ((gaussianKernel_derivative_joint_continuous n).comp hp.continuousOn hmap)
  have hh := continuousOn_integral_of_compact_support (μ := (volume : Measure (E m)))
    (f := fun r y => f y • iteratedFDeriv ℝ n (gaussianKernel r) (x - y)) (s := Ioi (0 : ℝ)) hfc hc
    (fun r y hr hy => by
      have hz : f y = 0 := by
        by_contra hn
        exact hy (subset_closure hn)
      simp only [hz, zero_smul])
  have he : (fun r : ℝ => iteratedFDeriv ℝ n (gaussianSmoothing r f) x) =
      fun r => ∫ y, f y • iteratedFDeriv ℝ n (gaussianKernel r) (x - y) := by
    funext r
    exact compact_convolution_iteratedFDeriv hf hfc (gaussianKernel_contDiff r) n x
  rw [he]
  exact hh

theorem gaussianSmoothing_scale_continuous {m : ℕ} {f : E m → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (x : E m) :
    ContinuousOn (fun r : ℝ => gaussianSmoothing r f x) (Ioi 0) :=
  fun r hr => (gaussianSmoothing_hasDerivAt_scale hr hf hfc x).continuousAt.continuousWithinAt

theorem gaussianSmoothing_norm_bound {m : ℕ} {f : E m → ℝ} {M r : ℝ} (hr : 0 < r)
    (hb : ∀ x, ‖f x‖ ≤ M) (x : E m) : ‖gaussianSmoothing r f x‖ ≤ M := by
  have he : gaussianSmoothing r f x = ∫ y, f (x - y) * gaussianKernel r y := by
    exact convolution_lsmul_swap (f := f) (g := gaussianKernel r) (μ := volume) (x := x)
  rw [he]
  have hbound : ∀ᵐ y ∂volume, ‖f (x - y) * gaussianKernel r y‖ ≤ M * gaussianKernel r y := by
    filter_upwards [] with y
    rw [norm_mul, Real.norm_eq_abs (gaussianKernel r y), abs_of_pos (gaussianKernel_pos hr y)]
    exact mul_le_mul_of_nonneg_right (hb _) (gaussianKernel_pos hr y).le
  have hh := norm_integral_le_of_norm_le ((gaussianKernel_integrable hr.ne').const_mul M) hbound
  rwa [integral_const_mul, gaussianKernel_integral hr, mul_one] at hh

noncomputable def gaussianPotential {m : ℕ} (f : E m → ℝ) (x : E m) : ℝ :=
  ∫ r in Ioc (0 : ℝ) 1, r * gaussianSmoothing r f x

theorem gaussianPotential_integrable {m : ℕ} {f : E m → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (x : E m) :
    IntegrableOn (fun r : ℝ => r * gaussianSmoothing r f x) (Ioc 0 1) volume := by
  obtain ⟨M, hM, hb⟩ := (hfc.isCompact_range hf).isBounded.exists_pos_norm_le
  have hb' : ∀ y, ‖f y‖ ≤ M := fun y => hb _ (mem_range_self y)
  have hc : ContinuousOn (fun r : ℝ => r * gaussianSmoothing r f x) (Ioc 0 1) :=
    continuous_id.continuousOn.mul ((gaussianSmoothing_scale_continuous hf hfc x).mono Ioc_subset_Ioi_self)
  apply (integrableOn_const (s := Ioc (0 : ℝ) 1) (μ := volume) (C := M)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).mono'
  · exact hc.aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
    rw [norm_mul, Real.norm_eq_abs r, abs_of_pos hr.1]
    calc
      _ ≤ r * M := mul_le_mul_of_nonneg_left (gaussianSmoothing_norm_bound hr.1 hb' x) hr.1.le
      _ ≤ M := by nlinarith [hr.2]

theorem gaussianSmoothing_tendsto_zero {m : ℕ} {f : E m → ℝ} (hf : Integrable f volume)
    {x : E m} (hfx : ContinuousAt f x) :
    Tendsto (fun r : ℝ => gaussianSmoothing r f x) (𝓝[>] 0) (𝓝 (f x)) := by
  convert! (gaussianSmoothing_tendsto hf hfx).comp tendsto_inv_nhdsGT_zero using 1
  funext r
  simp only [Function.comp_apply, inv_inv]

/-- A compact C² function is its unit-scale Gaussian smoothing minus
the heat potential of its Laplacian. -/
theorem gaussian_heat_representation {m : ℕ} {f : E m → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (x : E m) :
    f x = gaussianSmoothing 1 f x - gaussianPotential (laplacian f) x := by
  have hi := gaussianPotential_integrable (laplacian_continuous hf) (laplacian_hasCompactSupport hfc) x
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0 : ℝ)) (b := 1)
    (by norm_num) (fun r hr => gaussianSmoothing_heat_equation hr.1 hf hfc x)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr hi)
    (gaussianSmoothing_tendsto_zero (hf.continuous.integrable_of_hasCompactSupport hfc) hf.continuous.continuousAt)
    (gaussianSmoothing_heat_equation (by norm_num : (0 : ℝ) < 1) hf hfc x).continuousAt.continuousWithinAt
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hh
  change gaussianPotential (laplacian f) x = gaussianSmoothing 1 f x - f x at hh
  linarith

end Submission.Obl.Entropy__smooth_gaussian_transport
