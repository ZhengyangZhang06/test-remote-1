import Submission.Obl.Entropy__smooth_gaussian_transport.GaussianPotential
import Submission.Obl.Entropy__smooth_gaussian_transport.ScaleIntegralHolder

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def gaussianHolderMoment (m n : ℕ) (α : ℝ) : ℝ :=
  ∫ y : E m, ‖y‖ ^ α * ‖iteratedFDeriv ℝ n Submission.Lib.EntropyRemainder.gaussianDensity y‖

theorem gaussianHolderMoment_nonneg (m n : ℕ) (α : ℝ) : 0 ≤ gaussianHolderMoment m n α :=
  integral_nonneg (fun y => mul_nonneg (Real.rpow_nonneg (norm_nonneg y) _) (norm_nonneg _))

theorem gaussian_scaled_derivative_bound {m : ℕ} {α C r : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    {f : E m → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hmod : ∀ x y, |f x - f y| ≤ C * ‖x - y‖ ^ α) (n : ℕ) (x : E m) :
    ‖r • iteratedFDeriv ℝ (n + 1) (gaussianSmoothing r f) x‖ ≤
      C * gaussianHolderMoment m (n + 1) α * r ^ (α - n) := by
  rw [norm_smul, Real.norm_eq_abs r, abs_of_pos hr]
  have hh := mul_le_mul_of_nonneg_left
    (gaussianSmoothing_derivative_holder_bound hr hα hα1 hC hf hfc hmod n x) hr.le
  apply hh.trans_eq
  change r * (C * (r ^ α / r ^ (n + 1)) * gaussianHolderMoment m (n + 1) α) = _
  rw [Real.rpow_sub hr, Real.rpow_natCast, pow_succ]
  field_simp
  <;> ring

theorem gaussian_scaled_derivative_lipschitz {m : ℕ} {α C r : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    {f : E m → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hmod : ∀ x y, |f x - f y| ≤ C * ‖x - y‖ ^ α) (n : ℕ) (x y : E m) :
    ‖r • iteratedFDeriv ℝ n (gaussianSmoothing r f) x -
        r • iteratedFDeriv ℝ n (gaussianSmoothing r f) y‖ ≤
      C * gaussianHolderMoment m (n + 1) α * r ^ (α - n) * ‖x - y‖ := by
  have hdn : ContDiff ℝ 1 (iteratedFDeriv ℝ n (gaussianSmoothing r f)) :=
    (gaussianSmoothing_contDiff r hf.locallyIntegrable hfc).iteratedFDeriv_right
      (by exact_mod_cast (le_top : (1 + n : ENat) ≤ ⊤))
  have hb (z : E m) : ‖fderiv ℝ (iteratedFDeriv ℝ n (gaussianSmoothing r f)) z‖ ≤
      C * (r ^ α / r ^ (n + 1)) * gaussianHolderMoment m (n + 1) α := by
    rw [norm_fderiv_iteratedFDeriv]
    exact gaussianSmoothing_derivative_holder_bound hr hα hα1 hC hf hfc hmod n z
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ (univ : Set (E m))) => hdn.differentiable_one z)
    (fun z _ => hb z) (convex_univ : Convex ℝ (univ : Set (E m))) (x := y) (y := x)
    (mem_univ y) (mem_univ x)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs r, abs_of_pos hr]
  apply (mul_le_mul_of_nonneg_left hh hr.le).trans_eq
  rw [Real.rpow_sub hr, Real.rpow_natCast, pow_succ]
  field_simp
  <;> ring

noncomputable def gaussianPotentialHessian {m : ℕ} (f : E m → ℝ) (x : E m) :
    E m [×2]→L[ℝ] ℝ :=
  ∫ r in Ioc (0 : ℝ) 1, r • iteratedFDeriv ℝ 2 (gaussianSmoothing r f) x

theorem gaussianPotentialHessian_integrable {m : ℕ} {α C : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    {f : E m → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hmod : ∀ x y, |f x - f y| ≤ C * ‖x - y‖ ^ α) (x : E m) :
    IntegrableOn (fun r : ℝ => r • iteratedFDeriv ℝ 2 (gaussianSmoothing r f) x) (Ioc 0 1) volume := by
  have hc : ContinuousOn (fun r : ℝ => r • iteratedFDeriv ℝ 2 (gaussianSmoothing r f) x) (Ioc 0 1) :=
    continuous_id.continuousOn.smul ((gaussianSmoothing_derivative_scale_continuous hf hfc 2 x).mono Ioc_subset_Ioi_self)
  have hi : IntegrableOn (fun r : ℝ => r ^ (α - 1)) (Ioc 0 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  apply (hi.const_mul (C * gaussianHolderMoment m 2 α)).mono'
  · exact hc.aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
    simpa only [Nat.cast_one] using gaussian_scaled_derivative_bound hr.1 hα hα1 hC hf hfc hmod 1 x

theorem gaussianPotentialHessian_holder {m : ℕ} {α C : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hC : 0 ≤ C)
    {f : E m → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hmod : ∀ x y, |f x - f y| ≤ C * ‖x - y‖ ^ α) (x y : E m) :
    ‖gaussianPotentialHessian f x - gaussianPotentialHessian f y‖ ≤
      (2 * (C * gaussianHolderMoment m 2 α) / α +
        (C * gaussianHolderMoment m 3 α) / (1 - α)) * ‖x - y‖ ^ α := by
  apply bounded_scale_integral_holder hα hα1
    (mul_nonneg hC (gaussianHolderMoment_nonneg m 2 α))
    (mul_nonneg hC (gaussianHolderMoment_nonneg m 3 α))
    (gaussianPotentialHessian_integrable hα hα1.le hC hf hfc hmod)
  · intro r hr z
    simpa only [Nat.cast_one] using gaussian_scaled_derivative_bound hr.1 hα hα1.le hC hf hfc hmod 1 z
  · intro r hr z w
    exact gaussian_scaled_derivative_lipschitz hr.1 hα hα1.le hC hf hfc hmod 2 z w

end Submission.Obl.Entropy__smooth_gaussian_transport
