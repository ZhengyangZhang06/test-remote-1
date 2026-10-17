import Submission.Obl.Entropy__gaussian_l2_poincare.RotationEstimate

set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.Entropy__gaussian_l2_poincare

open MeasureTheory ProbabilityTheory Set
open scoped Topology

/-- Centering bounds the second moment by the mean squared difference of two copies. -/
theorem centered_integral_sq_le_pair {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → F}
    (hf : MemLp f 2 μ) (hm : ∫ x, f x ∂μ = 0) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) ≤ ∫ p : α × α, ‖f p.2 - f p.1‖ ^ 2 ∂μ.prod μ := by
  have hfi : Integrable f μ := hf.integrable (by norm_num)
  have hp : Integrable (fun p : α × α => ‖f p.2 - f p.1‖ ^ 2) (μ.prod μ) :=
    ((hf.comp_snd μ).sub (hf.comp_fst μ)).integrable_norm_pow (by norm_num)
  rw [integral_prod _ hp]
  apply integral_mono (hf.integrable_norm_pow (by norm_num)) hp.integral_prod_left
  intro x
  have hx := norm_integral_sq_le_mass_mul_integral_norm_sq μ
    (hfi.sub (integrable_const (f x)))
    ((hf.sub (memLp_const (f x))).integrable_norm_pow (by norm_num))
  simpa [integral_sub hfi (integrable_const (f x)), hm] using hx

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure E} [IsGaussian μ]

/-- Circular interpolation preserves a centered Gaussian product. -/
theorem gaussian_rotation_preserving (hμ : ∫ x, x ∂μ = 0) (t : ℝ) :
    MeasurePreserving (ContinuousLinearMap.rotation t : E × E →L[ℝ] E × E) (μ.prod μ)
      (μ.prod μ) :=
  ⟨by fun_prop, IsGaussian.map_rotation_eq_self hμ t⟩

/-- The rotation energy is integrable whenever the derivative has a second moment. -/
theorem integrable_rotationEnergy {f : E → F}
    (hμ : ∫ x, x ∂μ = 0) (hD : Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) μ) (t : ℝ) :
    Integrable (rotationEnergy f t) (μ.prod μ) := by
  have hnorm : Integrable (fun x : E => ‖x‖ ^ 2) μ :=
    IsGaussian.memLp_two_id.integrable_norm_pow (by norm_num)
  convert (gaussian_rotation_preserving hμ t).integrable_comp_of_integrable
    (hD.mul_prod hnorm) using 1
  funext p
  simp [rotationEnergy, ContinuousLinearMap.rotation_apply]

/-- Rotational invariance separates the derivative energy and the Gaussian second moment. -/
theorem integral_rotationEnergy {f : E → F}
    (hμ : ∫ x, x ∂μ = 0) (hD : Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) μ) (t : ℝ) :
    (∫ p, rotationEnergy f t p ∂μ.prod μ) =
      (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ) * ∫ y : E, ‖y‖ ^ 2 ∂μ := by
  have hnorm : Integrable (fun x : E => ‖x‖ ^ 2) μ :=
    IsGaussian.memLp_two_id.integrable_norm_pow (by norm_num)
  have hp := (gaussian_rotation_preserving hμ t).map_eq
  have hi := integral_map (by fun_prop : AEMeasurable
      (ContinuousLinearMap.rotation t : E × E →L[ℝ] E × E) (μ.prod μ))
    (hp.symm ▸ (hD.mul_prod hnorm).aestronglyMeasurable)
  change (∫ p, (‖fderiv ℝ f p.1‖ ^ 2 * ‖p.2‖ ^ 2)
      ∂(μ.prod μ).map (ContinuousLinearMap.rotation t)) = _ at hi
  rw [hp] at hi
  simpa only [ContinuousLinearMap.rotation_apply, rotationEnergy] using
    hi.symm.trans (integral_prod_mul (fun x : E => ‖fderiv ℝ f x‖ ^ 2)
      (fun y : E => ‖y‖ ^ 2))

/-- The Gaussian rotation energy is jointly integrable in time and in the two points. -/
theorem integrable_time_rotationEnergy {f : E → F} (hf : ContDiff ℝ 1 f)
    (hμ : ∫ x, x ∂μ = 0) (hD : Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) μ) :
    Integrable (Function.uncurry (rotationEnergy f))
      ((volume.restrict (Ioc 0 (Real.pi / 2))).prod (μ.prod μ)) := by
  have hcont : Continuous (Function.uncurry (rotationEnergy f)) := by
    unfold rotationEnergy Function.uncurry
    exact (((hf.continuous_fderiv (by norm_num)).comp (by fun_prop)).norm.pow 2).mul
      ((by fun_prop : Continuous (fun p : ℝ × (E × E) =>
        (-Real.sin p.1) • p.2.1 + Real.cos p.1 • p.2.2)).norm.pow 2)
  apply (integrable_prod_iff hcont.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (integrable_rotationEnergy hμ hD), ?_⟩
  have heq : (fun t => ∫ p, ‖rotationEnergy f t p‖ ∂μ.prod μ) =
      fun _ : ℝ => (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ) * ∫ y : E, ‖y‖ ^ 2 ∂μ := by
    funext t
    simpa only [rotationEnergy, Real.norm_eq_abs, abs_mul, abs_sq] using
      integral_rotationEnergy hμ hD t
  change Integrable (fun t => ∫ p, ‖rotationEnergy f t p‖ ∂μ.prod μ) _
  rw [heq]
  exact integrable_const _

/-- A finite-constant Gaussian Poincare bound, sufficient for compactness of centered maps.
The constant is deliberately expressed using the second moment of the source measure. -/
theorem gaussian_poincare_finite {f : E → F} (hf : ContDiff ℝ 1 f)
    (hμ : ∫ x, x ∂μ = 0) (hmem : MemLp f 2 μ) (hm : ∫ x, f x ∂μ = 0)
    (hD : Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) ≤
      ((Real.pi / 2) ^ 2 * ∫ x : E, ‖x‖ ^ 2 ∂μ) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  have hpi : 0 ≤ Real.pi / 2 := by positivity
  have ht := integrable_time_rotationEnergy hf hμ hD
  have hp : Integrable (fun p : E × E => ‖f p.2 - f p.1‖ ^ 2) (μ.prod μ) :=
    ((hmem.comp_snd μ).sub (hmem.comp_fst μ)).integrable_norm_pow (by norm_num)
  calc
    _ ≤ ∫ p : E × E, ‖f p.2 - f p.1‖ ^ 2 ∂μ.prod μ :=
      centered_integral_sq_le_pair μ hmem hm
    _ ≤ ∫ p : E × E, (Real.pi / 2) *
        (∫ t in Ioc 0 (Real.pi / 2), rotationEnergy f t p) ∂μ.prod μ := by
      apply integral_mono hp (ht.integral_prod_right.const_mul (Real.pi / 2))
      intro p
      simpa only [intervalIntegral.integral_of_le hpi, Function.uncurry, Prod.mk.eta] using
        norm_sub_sq_le_rotationEnergy hf p.1 p.2
    _ = (Real.pi / 2) * (∫ t in Ioc 0 (Real.pi / 2),
        ∫ p : E × E, rotationEnergy f t p ∂μ.prod μ) := by
      rw [integral_const_mul, integral_integral_swap ht]
    _ = _ := by
      simp_rw [integral_rotationEnergy hμ hD]
      rw [integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
        sub_zero, ENNReal.toReal_ofReal hpi, smul_eq_mul]
      ring

end Submission.Obl.Entropy__gaussian_l2_poincare
