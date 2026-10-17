import Submission.Obl.Entropy__smooth_gaussian_transport.GaussianHolderMoments

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- The integral of an integrable derivative of an integrable function vanishes. -/
theorem integral_fderiv_eq_zero {m : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {g : E m → F} (hg : Differentiable ℝ g) (hi : Integrable g volume)
    (hdi : Integrable (fderiv ℝ g) volume) :
    (∫ x, fderiv ℝ g x) = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.integral_apply hdi]
  have hv : Integrable (fun x => fderiv ℝ g x v) volume :=
    (ContinuousLinearMap.apply ℝ F v).integrable_comp hdi
  have hh := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (f := fun _ : E m => (1 : ℝ)) (g := g) (v := v) (μ := volume)
    (by simpa using (integrable_zero (E m) F volume))
    (by simpa using hv) (by simpa using hi)
    (fun x _ => differentiableAt_const 1) (fun x _ => hg x)
  simpa using hh

theorem gaussianKernel_derivative_integrable {m : ℕ} {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Integrable (iteratedFDeriv ℝ n (gaussianKernel (m := m) r)) volume := by
  have hc : Continuous (iteratedFDeriv ℝ n (gaussianKernel (m := m) r)) :=
    (gaussianKernel_contDiff (n := (n : WithTop ENat)) r).continuous_iteratedFDeriv le_rfl
  apply (integrable_norm_iff hc.aestronglyMeasurable).mp
  simpa only [pow_zero, one_mul] using gaussianKernel_weighted_derivative_integrable hr 0 n

/-- Every positive-order Gaussian derivative has zero total mass. -/
theorem gaussianKernel_derivative_integral_zero {m : ℕ} {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (∫ x : E m, iteratedFDeriv ℝ (n + 1) (gaussianKernel r) x) = 0 := by
  have hgn : ContDiff ℝ 1 (iteratedFDeriv ℝ n (gaussianKernel (m := m) r)) :=
    (gaussianKernel_contDiff (n := ((⊤ : ENat) : WithTop ENat)) r).iteratedFDeriv_right
      (by exact_mod_cast (le_top : (1 + n : ENat) ≤ ⊤))
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.integral_apply (gaussianKernel_derivative_integrable hr (n + 1))]
  let g : E m → ℝ := fun x => iteratedFDeriv ℝ n (gaussianKernel r) x (Fin.tail v)
  have hgd : Differentiable ℝ g :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E m) ℝ (Fin.tail v)).differentiable.comp hgn.differentiable_one
  have hgi : Integrable g volume :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E m) ℝ (Fin.tail v)).integrable_comp
      (gaussianKernel_derivative_integrable hr n)
  have he (x : E m) : fderiv ℝ g x (v 0) =
      iteratedFDeriv ℝ (n + 1) (gaussianKernel r) x v := by
    exact (hgn.differentiable_one x).iteratedFDeriv_succ_apply_left'.symm
  have hvi : Integrable (fun x => fderiv ℝ g x (v 0)) volume := by
    simp_rw [he]
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (n + 1) => E m) ℝ v).integrable_comp
      (gaussianKernel_derivative_integrable hr (n + 1))
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun _ : E m => (1 : ℝ)) (g := g) (v := v 0) (μ := volume)
    (by simpa using (integrable_zero (E m) ℝ volume))
    (by simpa using hvi) (by simpa using hgi)
    (fun x _ => differentiableAt_const 1) (fun x _ => hgd x)
  simpa only [one_mul, he, fderiv_const, fderiv_fun_const, ContinuousLinearMap.zero_apply, zero_mul,
    integral_zero, neg_zero, Pi.zero_apply, ContinuousMultilinearMap.zero_apply] using hh

end Submission.Obl.Entropy__smooth_gaussian_transport
