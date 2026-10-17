import Submission.Obl.Entropy__smooth_gaussian_transport.CompactDifferentiation
import Submission.Obl.Entropy__smooth_gaussian_transport.GaussianCancellation

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace Convolution NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem gaussianSmoothing_iteratedFDeriv {m : ℕ} (r : ℝ) {f : E m → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (n : ℕ) (x : E m) :
    iteratedFDeriv ℝ n (gaussianSmoothing r f) x =
      ∫ y, f (x - y) • iteratedFDeriv ℝ n (gaussianKernel r) y := by
  have hh := compact_convolution_iteratedFDeriv hf hfc (gaussianKernel_contDiff r) n x
  change iteratedFDeriv ℝ n (gaussianSmoothing r f) x = _ at hh
  rw [hh]
  exact convolution_lsmul_swap (f := f) (g := iteratedFDeriv ℝ n (gaussianKernel r)) (μ := volume) (x := x)

/-- Subtracting the value at the center uses the zero mass of Gaussian derivatives. -/
theorem gaussianSmoothing_derivative_cancellation {m : ℕ} {r : ℝ} (hr : 0 < r)
    {f : E m → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (n : ℕ) (x : E m) :
    iteratedFDeriv ℝ (n + 1) (gaussianSmoothing r f) x =
      ∫ y, (f (x - y) - f x) • iteratedFDeriv ℝ (n + 1) (gaussianKernel r) y := by
  have hd : Continuous (iteratedFDeriv ℝ (n + 1) (gaussianKernel (m := m) r)) :=
    (gaussianKernel_contDiff (n := ((n + 1 : ℕ) : WithTop ENat)) r).continuous_iteratedFDeriv le_rfl
  have hi : Integrable (fun y => f (x - y) • iteratedFDeriv ℝ (n + 1) (gaussianKernel r) y) volume := by
    apply ((hf.comp (continuous_const.sub continuous_id)).smul hd).integrable_of_hasCompactSupport
    convert! (hfc.comp_homeomorph (Homeomorph.subLeft x)).smul_right using 1
  simp_rw [sub_smul]
  have hj : Integrable (fun y : E m => f x • iteratedFDeriv ℝ (n + 1) (gaussianKernel r) y) volume := by
    exact (gaussianKernel_derivative_integrable (m := m) hr (n + 1)).smul (f x)
  rw [integral_sub hi hj,
    integral_smul, gaussianKernel_derivative_integral_zero hr n, smul_zero, sub_zero]
  exact gaussianSmoothing_iteratedFDeriv r hf hfc (n + 1) x

/-- A Hölder modulus gains the factor r^α in every positive-order
Gaussian smoothing derivative estimate. -/
theorem gaussianSmoothing_derivative_holder_bound {m : ℕ} {r α C : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    {f : E m → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hmod : ∀ x y, |f x - f y| ≤ C * ‖x - y‖ ^ α) (n : ℕ) (x : E m) :
    ‖iteratedFDeriv ℝ (n + 1) (gaussianSmoothing r f) x‖ ≤
      C * (r ^ α / r ^ (n + 1)) * ∫ y : E m, ‖y‖ ^ α *
        ‖iteratedFDeriv ℝ (n + 1) Submission.Lib.EntropyRemainder.gaussianDensity y‖ := by
  rw [gaussianSmoothing_derivative_cancellation hr hf hfc n x]
  have hb : ∀ y : E m,
      ‖(f (x - y) - f x) • iteratedFDeriv ℝ (n + 1) (gaussianKernel r) y‖ ≤
        C * (‖y‖ ^ α * ‖iteratedFDeriv ℝ (n + 1) (gaussianKernel r) y‖) := by
    intro y
    rw [norm_smul, Real.norm_eq_abs]
    have hm := hmod (x - y) x
    have he : x - y - x = -y := by abel
    rw [he, norm_neg] at hm
    calc
      _ ≤ (C * ‖y‖ ^ α) * ‖iteratedFDeriv ℝ (n + 1) (gaussianKernel r) y‖ :=
        mul_le_mul_of_nonneg_right hm (norm_nonneg _)
      _ = _ := mul_assoc _ _ _
  have hi := (gaussianKernel_holder_derivative_integrable (m := m) hr hα hα1 (n + 1)).const_mul C
  have hh := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hb)
  rw [integral_const_mul, gaussianKernel_holder_derivative_integral hr α (n + 1)] at hh
  simpa only [mul_assoc] using hh

end Submission.Obl.Entropy__smooth_gaussian_transport
