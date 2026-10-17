import Submission.Obl.Entropy__continuous_jacobian_of_l2_limit.GaussianDensity

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology ENNReal

namespace Submission.Obl.Entropy__continuous_jacobian_of_l2_limit

variable {m : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
local notation "E" => EuclideanSpace ℝ (Fin m)

lemma integrable_density_smul {f : E → Y} (hf : Integrable f (stdGaussian E)) :
    Integrable (fun x => gaussianDensity x • f x) volume := by
  rw [stdGaussian_eq_withDensity] at hf
  have h := (integrable_withDensity_iff_integrable_smul'
    continuous_gaussianDensity.measurable.ennreal_ofReal
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)).mp hf
  simpa only [ENNReal.toReal_ofReal (gaussianDensity_pos _).le] using h

lemma locallyIntegrable_of_integrable_gaussian {f : E → Y}
    (hf : Integrable f (stdGaussian E)) : LocallyIntegrable f volume := by
  have h := (integrable_density_smul hf).locallyIntegrable.continuous_smul
    (continuous_gaussianDensity.inv₀ fun x => (gaussianDensity_pos x).ne')
  simpa only [Pi.inv_apply, smul_smul, inv_mul_cancel₀ (gaussianDensity_pos _).ne', one_smul] using h

lemma integral_gaussian_eq_density {f : E → ℝ} :
    (∫ x, f x ∂stdGaussian E) = ∫ x, gaussianDensity x * f x := by
  rw [stdGaussian_eq_withDensity, integral_withDensity_eq_integral_toReal_smul
    continuous_gaussianDensity.measurable.ennreal_ofReal
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (gaussianDensity_pos _).le, smul_eq_mul]

/-- On a compact set the Lebesgue L1 norm is controlled by the Gaussian L1 norm. -/
lemma compact_integral_norm_le_gaussian (K : Set E) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : E → Y, Integrable f (stdGaussian E) →
      (∫ x in K, ‖f x‖) ≤ C * ∫ x, ‖f x‖ ∂stdGaussian E := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (continuous_gaussianDensity.inv₀ fun x => (gaussianDensity_pos x).ne').continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro f hf
  have hw : Integrable (fun x => gaussianDensity x * ‖f x‖) volume :=
    integrable_density_smul hf.norm
  rw [integral_gaussian_eq_density]
  calc
    (∫ x in K, ‖f x‖) ≤ ∫ x in K, max C 0 * (gaussianDensity x * ‖f x‖) := by
      apply setIntegral_mono_on
        ((locallyIntegrable_of_integrable_gaussian hf).integrableOn_isCompact hK).norm
        (hw.const_mul _).restrict hK.measurableSet
      intro x hx
      have hi : (gaussianDensity x)⁻¹ ≤ max C 0 :=
        (le_abs_self _).trans ((hC x hx).trans (le_max_left _ _))
      calc
        ‖f x‖ = (gaussianDensity x)⁻¹ * (gaussianDensity x * ‖f x‖) := by
          rw [← mul_assoc, inv_mul_cancel₀ (gaussianDensity_pos x).ne', one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right hi
          (mul_nonneg (gaussianDensity_pos x).le (norm_nonneg _))
    _ = max C 0 * ∫ x in K, gaussianDensity x * ‖f x‖ := integral_const_mul _ _
    _ ≤ max C 0 * ∫ x, gaussianDensity x * ‖f x‖ :=
      mul_le_mul_of_nonneg_left (setIntegral_le_integral hw
        (ae_of_all _ fun x => mul_nonneg (gaussianDensity_pos x).le (norm_nonneg _)))
        (le_max_right _ _)

lemma integral_norm_le_sqrt_integral_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → Y} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ fun x => norm_nonneg (f x)) (ae_of_all μ fun _ => (show (0 : ℝ) ≤ 1 by norm_num))
    (by simpa using hf.norm) (by simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : α => (1 : ℝ)) 2 μ))
  simpa [Real.rpow_two, Real.sqrt_eq_rpow] using h

lemma localL1_of_gaussianL2 {u : ℕ → E → Y} {f : E → Y}
    (hu : ∀ n, MemLp (u n) 2 (stdGaussian E)) (hf : MemLp f 2 (stdGaussian E))
    (hlim : Tendsto (fun n => ∫ x, ‖u n x - f x‖ ^ 2 ∂stdGaussian E) atTop (𝓝 0))
    (K : Set E) (hK : IsCompact K) :
    Tendsto (fun n => ∫ x in K, ‖u n x - f x‖) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := compact_integral_norm_le_gaussian (Y := Y) K hK
  have ht : Tendsto (fun n => C * Real.sqrt (∫ x, ‖u n x - f x‖ ^ 2 ∂stdGaussian E))
      atTop (𝓝 0) := by
    simpa using (hlim.sqrt.const_mul C)
  apply squeeze_zero (fun n => integral_nonneg fun _ => norm_nonneg _) _ ht
  intro n
  exact (hbound _ (((hu n).sub hf).integrable (by norm_num))).trans
    (mul_le_mul_of_nonneg_left (integral_norm_le_sqrt_integral_sq ((hu n).sub hf)) hC)

end Submission.Obl.Entropy__continuous_jacobian_of_l2_limit
