import Submission.Obl.Entropy__smooth_gaussian_transport.GaussianKernelMoments

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

private theorem rpow_le_one_add {α r : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hr : 0 ≤ r) :
    r ^ α ≤ 1 + r := by
  by_cases hr1 : r ≤ 1
  · exact (Real.rpow_le_one hr hr1 hα).trans (by linarith)
  · exact (Real.rpow_le_self_of_one_le (le_of_not_ge hr1) hα1).trans (by linarith)

theorem gaussianDensity_holder_derivative_integrable {m : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) :
    Integrable (fun x : E m => ‖x‖ ^ α *
      ‖iteratedFDeriv ℝ n Submission.Lib.EntropyRemainder.gaussianDensity x‖) volume := by
  have h0 := gaussianDensity_weighted_derivative_integrable (m := m) 0 n
  have h1 := gaussianDensity_weighted_derivative_integrable (m := m) 1 n
  simp only [pow_zero, one_mul] at h0
  simp only [pow_one] at h1
  have hd : Continuous (iteratedFDeriv ℝ n (Submission.Lib.EntropyRemainder.gaussianDensity (m := m))) :=
    (Submission.Lib.EntropyRemainder.gaussianDensity_contDiff (n := (n : WithTop ENat))).continuous_iteratedFDeriv le_rfl
  apply (h0.add h1).mono'
  · exact ((measurable_norm.pow_const α).mul hd.norm.measurable).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg x) _) (norm_nonneg _))]
    have hb := mul_le_mul_of_nonneg_right (rpow_le_one_add hα.le hα1 (norm_nonneg x))
      (norm_nonneg (iteratedFDeriv ℝ n Submission.Lib.EntropyRemainder.gaussianDensity x))
    simpa only [add_mul, one_mul, Pi.add_apply] using hb

private theorem holder_kernel_scaling {m : ℕ} {r : ℝ} (hr : 0 < r) (α : ℝ) (n : ℕ) (x : E m) :
    ‖x‖ ^ α * ‖iteratedFDeriv ℝ n (gaussianKernel r) x‖ =
      (r ^ α / r ^ (m + n)) *
        (‖r⁻¹ • x‖ ^ α * ‖iteratedFDeriv ℝ n
          Submission.Lib.EntropyRemainder.gaussianDensity (r⁻¹ • x)‖) := by
  rw [gaussianKernel_iteratedFDeriv, norm_smul, norm_smul]
  simp only [Real.norm_eq_abs, abs_inv, abs_of_pos hr, abs_of_pos (pow_pos hr _)]
  rw [Real.mul_rpow (inv_nonneg.mpr hr.le) (norm_nonneg x), Real.inv_rpow hr.le]
  field_simp [(Real.rpow_pos_of_pos hr α).ne']

theorem gaussianKernel_holder_derivative_integrable {m : ℕ} {r α : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) :
    Integrable (fun x : E m => ‖x‖ ^ α * ‖iteratedFDeriv ℝ n (gaussianKernel r) x‖) volume := by
  have hi := ((integrable_comp_smul_iff volume
    (fun x : E m => ‖x‖ ^ α * ‖iteratedFDeriv ℝ n
      Submission.Lib.EntropyRemainder.gaussianDensity x‖) (inv_ne_zero hr.ne')).mpr
    (gaussianDensity_holder_derivative_integrable hα hα1 n)).const_mul (r ^ α / r ^ (m + n))
  exact hi.congr (Filter.Eventually.of_forall (fun x => (holder_kernel_scaling hr α n x).symm))

/-- The exact weighted moment of order α gives the scale r^(α-n) in
Hölder estimates for Gaussian regularization. -/
theorem gaussianKernel_holder_derivative_integral {m : ℕ} {r : ℝ} (hr : 0 < r) (α : ℝ) (n : ℕ) :
    ∫ x : E m, ‖x‖ ^ α * ‖iteratedFDeriv ℝ n (gaussianKernel r) x‖ =
      (r ^ α / r ^ n) * ∫ x : E m, ‖x‖ ^ α *
        ‖iteratedFDeriv ℝ n Submission.Lib.EntropyRemainder.gaussianDensity x‖ := by
  simp_rw [holder_kernel_scaling hr α n]
  rw [integral_const_mul]
  have hi : (∫ x : E m, ‖r⁻¹ • x‖ ^ α * ‖iteratedFDeriv ℝ n
      Submission.Lib.EntropyRemainder.gaussianDensity (r⁻¹ • x)‖) =
      r ^ Module.finrank ℝ (E m) * ∫ x : E m, ‖x‖ ^ α *
        ‖iteratedFDeriv ℝ n Submission.Lib.EntropyRemainder.gaussianDensity x‖ := by
    convert! Measure.integral_comp_inv_smul_of_nonneg volume
      (fun x : E m => ‖x‖ ^ α * ‖iteratedFDeriv ℝ n
        Submission.Lib.EntropyRemainder.gaussianDensity x‖) hr.le using 1
  rw [hi]
  simp only [E, finrank_euclideanSpace_fin, pow_add]
  field_simp

end Submission.Obl.Entropy__smooth_gaussian_transport
