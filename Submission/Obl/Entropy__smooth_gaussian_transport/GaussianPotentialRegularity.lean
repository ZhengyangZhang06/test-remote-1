import Submission.Obl.Entropy__smooth_gaussian_transport.GaussianPotentialEstimates
import Submission.Obl.Entropy__smooth_gaussian_transport.DominatedSecondDerivative

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem gaussianSmoothing_fderiv_scale_continuous {m : ℕ} {f : E m → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (x : E m) :
    ContinuousOn (fun r : ℝ => fderiv ℝ (gaussianSmoothing r f) x) (Ioi 0) := by
  apply continuousOn_clm_apply.mpr
  intro v
  have hh := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => E m) ℝ (fun _ => v)).continuous.comp_continuousOn
    (gaussianSmoothing_derivative_scale_continuous hf hfc 1 x)
  convert! hh using 1
  funext r
  simp only [Function.comp_apply, ContinuousMultilinearMap.apply_apply, iteratedFDeriv_one_apply]

theorem gaussianSmoothing_second_fderiv_scale_continuous {m : ℕ} {f : E m → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (x : E m) :
    ContinuousOn (fun r : ℝ => fderiv ℝ (fderiv ℝ (gaussianSmoothing r f)) x) (Ioi 0) := by
  apply continuousOn_clm_apply.mpr
  intro v
  apply continuousOn_clm_apply.mpr
  intro w
  have hh := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E m) ℝ ![v, w]).continuous.comp_continuousOn
    (gaussianSmoothing_derivative_scale_continuous hf hfc 2 x)
  convert! hh using 1
  funext r
  simp only [Function.comp_apply, ContinuousMultilinearMap.apply_apply, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The heat potential of a compact Hölder function is C², and its second
iterated derivative is the absolutely convergent differentiated kernel integral. -/
theorem gaussianPotential_contDiff_two {m : ℕ} {α C : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    {f : E m → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hmod : ∀ x y, |f x - f y| ≤ C * ‖x - y‖ ^ α) :
    ContDiff ℝ 2 (gaussianPotential f) ∧
      ∀ x, iteratedFDeriv ℝ 2 (gaussianPotential f) x = gaussianPotentialHessian f x := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 1)
  let F : ℝ → E m → ℝ := fun r x => r * gaussianSmoothing r f x
  let F₁ : ℝ → E m → E m →L[ℝ] ℝ := fun r x => r • fderiv ℝ (gaussianSmoothing r f) x
  let F₂ : ℝ → E m → E m →L[ℝ] (E m →L[ℝ] ℝ) :=
    fun r x => r • fderiv ℝ (fderiv ℝ (gaussianSmoothing r f)) x
  obtain ⟨M, hM, hb⟩ := (hfc.isCompact_range hf).isBounded.exists_pos_norm_le
  have hb' : ∀ y, ‖f y‖ ≤ M := fun y => hb _ (mem_range_self y)
  have hi₀ : Integrable (fun _ : ℝ => M) μ := by
    exact integrableOn_const (s := Ioc (0 : ℝ) 1) (μ := volume) (C := M)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hi₁ : Integrable (fun r : ℝ => (C * gaussianHolderMoment m 1 α) * r ^ α) μ := by
    have hi : IntegrableOn (fun r : ℝ => r ^ α) (Ioc 0 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    exact hi.const_mul _
  have hi₂ : Integrable (fun r : ℝ => (C * gaussianHolderMoment m 2 α) * r ^ (α - 1)) μ := by
    have hi : IntegrableOn (fun r : ℝ => r ^ (α - 1)) (Ioc 0 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    exact hi.const_mul _
  have hm₀ (x : E m) : AEStronglyMeasurable (fun r => F r x) μ :=
    (continuous_id.continuousOn.mul ((gaussianSmoothing_scale_continuous hf hfc x).mono
      Ioc_subset_Ioi_self)).aestronglyMeasurable measurableSet_Ioc
  have hm₁ (x : E m) : AEStronglyMeasurable (fun r => F₁ r x) μ :=
    (continuous_id.continuousOn.smul ((gaussianSmoothing_fderiv_scale_continuous hf hfc x).mono
      Ioc_subset_Ioi_self)).aestronglyMeasurable measurableSet_Ioc
  have hm₂ (x : E m) : AEStronglyMeasurable (fun r => F₂ r x) μ :=
    (continuous_id.continuousOn.smul ((gaussianSmoothing_second_fderiv_scale_continuous hf hfc x).mono
      Ioc_subset_Ioi_self)).aestronglyMeasurable measurableSet_Ioc
  have hmem : ∀ᵐ r ∂μ, r ∈ Ioc (0 : ℝ) 1 := self_mem_ae_restrict measurableSet_Ioc
  have hb₀ : ∀ᵐ r ∂μ, ∀ x, ‖F r x‖ ≤ M := by
    filter_upwards [hmem] with r hr
    intro x
    dsimp only [F]
    rw [norm_mul, Real.norm_eq_abs r, abs_of_pos hr.1]
    exact (mul_le_mul_of_nonneg_left (gaussianSmoothing_norm_bound hr.1 hb' x) hr.1.le).trans
      (by nlinarith [hr.2])
  have hb₁ : ∀ᵐ r ∂μ, ∀ x, ‖F₁ r x‖ ≤ (C * gaussianHolderMoment m 1 α) * r ^ α := by
    filter_upwards [hmem] with r hr
    intro x
    have hh := gaussian_scaled_derivative_bound hr.1 hα hα1 hC hf hfc hmod 0 x
    change ‖r • fderiv ℝ (gaussianSmoothing r f) x‖ ≤ _
    simpa only [norm_smul, Nat.reduceAdd, norm_iteratedFDeriv_one, Nat.cast_zero, sub_zero] using hh
  have hb₂ : ∀ᵐ r ∂μ, ∀ x, ‖F₂ r x‖ ≤ (C * gaussianHolderMoment m 2 α) * r ^ (α - 1) := by
    filter_upwards [hmem] with r hr
    intro x
    have hh := gaussian_scaled_derivative_bound hr.1 hα hα1 hC hf hfc hmod 1 x
    have he : ‖fderiv ℝ (fderiv ℝ (gaussianSmoothing r f)) x‖ =
        ‖iteratedFDeriv ℝ 2 (gaussianSmoothing r f) x‖ := by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    change ‖r • fderiv ℝ (fderiv ℝ (gaussianSmoothing r f)) x‖ ≤ _
    rw [norm_smul_clm, he]
    simpa only [norm_smul, Nat.reduceAdd, Nat.cast_one] using hh
  have hs (r : ℝ) : ContDiff ℝ 3 (gaussianSmoothing r f) :=
    (gaussianSmoothing_contDiff r hf.locallyIntegrable hfc).of_le
      (WithTop.coe_le_coe.mpr (le_top : (3 : ENat) ≤ ⊤))
  have hd₀ : ∀ᵐ r ∂μ, ∀ x, HasFDerivAt (F r) (F₁ r x) x := by
    filter_upwards [] with r
    intro x
    exact ((hs r).differentiable (by norm_num) x).hasFDerivAt.const_smul r
  have hd₁ : ∀ᵐ r ∂μ, ∀ x, HasFDerivAt (F₁ r) (F₂ r x) x := by
    filter_upwards [] with r
    intro x
    have hd : ContDiff ℝ 2 (fderiv ℝ (gaussianSmoothing r f)) := (hs r).fderiv_right (by norm_num)
    exact (hd.differentiable (by norm_num) x).hasFDerivAt.const_smul r
  have hc₂ : ∀ᵐ r ∂μ, Continuous (F₂ r) := by
    filter_upwards [] with r
    have hd : ContDiff ℝ 2 (fderiv ℝ (gaussianSmoothing r f)) := (hs r).fderiv_right (by norm_num)
    exact (hd.continuous_fderiv (by norm_num)).const_smul r
  obtain ⟨hreg, hder, hsecond⟩ := integral_contDiff_two_of_dominated hi₀ hi₁ hi₂
    hm₀ hm₁ hm₂ hb₀ hb₁ hb₂ hd₀ hd₁ hc₂
  refine ⟨hreg, ?_⟩
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  rw [iteratedFDeriv_two_apply]
  change fderiv ℝ (fderiv ℝ (fun x => ∫ r, F r x ∂μ)) x (v 0) (v 1) = _
  rw [hsecond]
  change (∫ r in Ioc (0 : ℝ) 1, (F₂ r x (v 0)) (v 1)) = gaussianPotentialHessian f x v
  rw [gaussianPotentialHessian, ContinuousMultilinearMap.integral_apply
    (gaussianPotentialHessian_integrable hα hα1 hC hf hfc hmod x)]
  apply integral_congr_ae
  filter_upwards [] with r
  simp only [F₂, smul_apply, iteratedFDeriv_two_apply]

end Submission.Obl.Entropy__smooth_gaussian_transport
