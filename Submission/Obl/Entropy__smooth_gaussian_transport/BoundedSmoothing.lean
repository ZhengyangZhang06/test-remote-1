import Submission.Obl.Entropy__smooth_gaussian_transport.GaussianPotentialEstimates

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem gaussianSmoothing_one_derivative_bound {m : ℕ} {f : E m → ℝ} {M : ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hb : ∀ x, ‖f x‖ ≤ M) (n : ℕ) (x : E m) :
    ‖iteratedFDeriv ℝ n (gaussianSmoothing 1 f) x‖ ≤ M * gaussianHolderMoment m n 0 := by
  rw [gaussianSmoothing_iteratedFDeriv 1 hf hfc n x]
  have hbound : ∀ᵐ y ∂volume,
      ‖f (x - y) • iteratedFDeriv ℝ n (gaussianKernel 1) y‖ ≤
        M * ‖iteratedFDeriv ℝ n (gaussianKernel 1) y‖ := by
    filter_upwards [] with y
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)
  have hh := norm_integral_le_of_norm_le
    ((gaussianKernel_derivative_integrable (m := m) (by norm_num : (0 : ℝ) < 1) n).norm.const_mul M) hbound
  rw [integral_const_mul] at hh
  convert! hh using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [gaussianKernel_iteratedFDeriv, one_pow, inv_one, one_smul, Real.rpow_zero, one_mul]

/-- Unit-scale smoothing has a uniform Hölder Hessian bound depending only
on the size of the unsmoothed function. -/
theorem gaussianSmoothing_one_hessian_holder {m : ℕ} {f : E m → ℝ} {M α : ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hM : 0 ≤ M)
    (hb : ∀ x, ‖f x‖ ≤ M) (hα : 0 < α) (hα1 : α ≤ 1) (x y : E m) :
    ‖iteratedFDeriv ℝ 2 (gaussianSmoothing 1 f) x - iteratedFDeriv ℝ 2 (gaussianSmoothing 1 f) y‖ ≤
      M * (gaussianHolderMoment m 3 0 + 2 * gaussianHolderMoment m 2 0) * ‖x - y‖ ^ α := by
  have hdn : ContDiff ℝ 1 (iteratedFDeriv ℝ 2 (gaussianSmoothing 1 f)) :=
    (gaussianSmoothing_contDiff 1 hf.locallyIntegrable hfc).iteratedFDeriv_right
      (WithTop.coe_le_coe.mpr (le_top : (1 + 2 : ENat) ≤ ⊤))
  have hder (z : E m) : ‖fderiv ℝ (iteratedFDeriv ℝ 2 (gaussianSmoothing 1 f)) z‖ ≤
      M * gaussianHolderMoment m 3 0 := by
    rw [norm_fderiv_iteratedFDeriv]
    exact gaussianSmoothing_one_derivative_bound hf hfc hb 3 z
  have h2 := gaussianHolderMoment_nonneg m 2 0
  have h3 := gaussianHolderMoment_nonneg m 3 0
  by_cases hd : ‖x - y‖ ≤ 1
  · have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z (_ : z ∈ (univ : Set (E m))) => hdn.differentiable_one z)
      (fun z _ => hder z) (convex_univ : Convex ℝ (univ : Set (E m))) (x := y) (y := x)
      (mem_univ y) (mem_univ x)
    have hp : ‖x - y‖ ≤ ‖x - y‖ ^ α := by
      by_cases hz : x = y
      · subst y
        simp only [sub_self, norm_zero, Real.zero_rpow hα.ne', le_refl]
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge
        (norm_pos_iff.mpr (sub_ne_zero.mpr hz)) hd hα1
    calc
      _ ≤ (M * gaussianHolderMoment m 3 0) * ‖x - y‖ := hh
      _ ≤ (M * gaussianHolderMoment m 3 0) * ‖x - y‖ ^ α :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg hM h3)
      _ ≤ _ := by gcongr; nlinarith
  · have hp : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow (le_of_not_ge hd) hα.le
    calc
      _ ≤ ‖iteratedFDeriv ℝ 2 (gaussianSmoothing 1 f) x‖ +
          ‖iteratedFDeriv ℝ 2 (gaussianSmoothing 1 f) y‖ := norm_sub_le _ _
      _ ≤ M * gaussianHolderMoment m 2 0 + M * gaussianHolderMoment m 2 0 :=
        add_le_add (gaussianSmoothing_one_derivative_bound hf hfc hb 2 x)
          (gaussianSmoothing_one_derivative_bound hf hfc hb 2 y)
      _ ≤ M * (gaussianHolderMoment m 3 0 + 2 * gaussianHolderMoment m 2 0) := by nlinarith
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hM (by positivity)) hp

end Submission.Obl.Entropy__smooth_gaussian_transport
