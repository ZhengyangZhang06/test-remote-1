import Submission.Obl.Entropy__smooth_gaussian_transport.GaussianSchwartz

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem gaussianKernel_iteratedFDeriv {m : ℕ} (r : ℝ) (n : ℕ) (x : E m) :
    iteratedFDeriv ℝ n (gaussianKernel r) x =
      (r ^ (m + n))⁻¹ • iteratedFDeriv ℝ n
        Submission.Lib.EntropyRemainder.gaussianDensity (r⁻¹ • x) := by
  have hg : ContDiff ℝ n (Submission.Lib.EntropyRemainder.gaussianDensity (m := m)) :=
    Submission.Lib.EntropyRemainder.gaussianDensity_contDiff
  have hs : ContDiff ℝ n (fun x : E m => r⁻¹ • x) := by
    convert! (r⁻¹ • ContinuousLinearMap.id ℝ (E m)).contDiff using 1
  have hf : gaussianKernel (m := m) r = fun x => (r ^ m)⁻¹ •
      Submission.Lib.EntropyRemainder.gaussianDensity (r⁻¹ • x) := rfl
  have hc : ContDiff ℝ n (fun y : E m =>
      Submission.Lib.EntropyRemainder.gaussianDensity (r⁻¹ • y)) := by convert! hg.comp hs using 1
  have hsm : iteratedFDeriv ℝ n (fun y : E m => (r ^ m)⁻¹ •
      Submission.Lib.EntropyRemainder.gaussianDensity (r⁻¹ • y)) x =
      (r ^ m)⁻¹ • iteratedFDeriv ℝ n (fun y : E m =>
        Submission.Lib.EntropyRemainder.gaussianDensity (r⁻¹ • y)) x := by
    convert! iteratedFDeriv_const_smul_apply' (a := (r ^ m)⁻¹) hc.contDiffAt using 1
  rw [hf, hsm, iteratedFDeriv_comp_const_smul r⁻¹ hg, smul_smul]
  congr 1
  simp only [pow_add, mul_inv_rev, inv_pow]
  ring

private theorem weighted_kernel_scaling {m : ℕ} {r : ℝ} (hr : 0 < r) (k n : ℕ) (x : E m) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (gaussianKernel r) x‖ =
      (r ^ k / r ^ (m + n)) *
        (‖r⁻¹ • x‖ ^ k * ‖iteratedFDeriv ℝ n
          Submission.Lib.EntropyRemainder.gaussianDensity (r⁻¹ • x)‖) := by
  rw [gaussianKernel_iteratedFDeriv, norm_smul, norm_smul]
  simp only [Real.norm_eq_abs, abs_inv, abs_of_pos hr, abs_of_pos (pow_pos hr _), mul_pow, inv_pow]
  field_simp

/-- Every polynomially weighted derivative of every positive-scale Gaussian
kernel is integrable. -/
theorem gaussianKernel_weighted_derivative_integrable {m : ℕ} {r : ℝ} (hr : 0 < r) (k n : ℕ) :
    Integrable (fun x : E m => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (gaussianKernel r) x‖) volume := by
  have hi := ((integrable_comp_smul_iff volume
    (fun x : E m => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n
      Submission.Lib.EntropyRemainder.gaussianDensity x‖) (inv_ne_zero hr.ne')).mpr
    (gaussianDensity_weighted_derivative_integrable k n)).const_mul (r ^ k / r ^ (m + n))
  exact hi.congr (Filter.Eventually.of_forall (fun x => (weighted_kernel_scaling hr k n x).symm))

/-- The weighted L1 norms have the expected exact scale r^(k-n). -/
theorem gaussianKernel_weighted_derivative_integral {m : ℕ} {r : ℝ} (hr : 0 < r) (k n : ℕ) :
    ∫ x : E m, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (gaussianKernel r) x‖ =
      (r ^ k / r ^ n) * ∫ x : E m, ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n Submission.Lib.EntropyRemainder.gaussianDensity x‖ := by
  simp_rw [weighted_kernel_scaling hr k n]
  rw [integral_const_mul]
  have hi : (∫ x : E m, ‖r⁻¹ • x‖ ^ k * ‖iteratedFDeriv ℝ n
      Submission.Lib.EntropyRemainder.gaussianDensity (r⁻¹ • x)‖) =
      r ^ Module.finrank ℝ (E m) * ∫ x : E m, ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n Submission.Lib.EntropyRemainder.gaussianDensity x‖ := by
    convert! Measure.integral_comp_inv_smul_of_nonneg volume
      (fun x : E m => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n
        Submission.Lib.EntropyRemainder.gaussianDensity x‖) hr.le using 1
  rw [hi]
  simp only [E, finrank_euclideanSpace_fin, smul_eq_mul, pow_add]
  field_simp

end Submission.Obl.Entropy__smooth_gaussian_transport
