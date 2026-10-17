import Submission.Lib.EntropyTools.DensityMoments

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Submission.Obl.Entropy__gaussian_covariance_variational

variable {m : ℕ}

/-- A continuous transport of a density with finite second moment is Gaussian L2. -/
theorem transport_memLp
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2) volume)
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hF : Continuous F)
    (hlaw : Measure.map F (stdGaussian (EuclideanSpace ℝ (Fin m))) =
      volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    MemLp F 2 (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  have hid : MemLp (id : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) 2
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) := by
    apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
    apply (integrable_withDensity_iff_integrable_smul₀'
      hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal (by simp)).2
    simpa only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul, id_eq] using hf2
  rw [← hlaw] at hid
  exact (memLp_map_measure_iff continuous_id.aestronglyMeasurable
    hF.measurable.aemeasurable).1 hid

/-- The Gaussian mean agrees with the Bochner mean of the target density. -/
theorem transport_mean
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hF : Continuous F)
    (hlaw : Measure.map F (stdGaussian (EuclideanSpace ℝ (Fin m))) =
      volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    ∫ x, F x ∂stdGaussian (EuclideanSpace ℝ (Fin m)) = ∫ x, f x • x := by
  calc
    _ = ∫ x, id x ∂Measure.map F (stdGaussian (EuclideanSpace ℝ (Fin m))) :=
      (integral_map hF.measurable.aemeasurable continuous_id.aestronglyMeasurable).symm
    _ = ∫ x, f x • x := by
      rw [hlaw, integral_withDensity_eq_integral_toReal_smul₀
        hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal (by simp)]
      simp only [ENNReal.toReal_ofReal (hf0 _), id_eq]

/-- Scalar continuous observables may be integrated on either side of the law. -/
theorem transport_integral
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hF : Continuous F)
    (hlaw : Measure.map F (stdGaussian (EuclideanSpace ℝ (Fin m))) =
      volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {g : EuclideanSpace ℝ (Fin m) → ℝ} (hg : Continuous g) :
    ∫ x, g (F x) ∂stdGaussian (EuclideanSpace ℝ (Fin m)) = ∫ x, f x * g x := by
  calc
    _ = ∫ x, g x ∂Measure.map F (stdGaussian (EuclideanSpace ℝ (Fin m))) :=
      (integral_map hF.measurable.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ x, f x * g x := by
      rw [hlaw, integral_withDensity_eq_integral_toReal_smul₀
        hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal (by simp)]
      simp only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul]

/-- The frozen density covariance is the covariance of the transport itself. -/
theorem transport_covariance
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hF : Continuous F)
    (hlaw : Measure.map F (stdGaussian (EuclideanSpace ℝ (Fin m))) =
      volume.withDensity (fun x => ENNReal.ofReal (f x))) (i j : Fin m) :
    (∫ x, f x * (x i - (∫ y, f y • y) i) * (x j - (∫ y, f y • y) j)) =
      ∫ x, (F x i - (∫ y, F y ∂stdGaussian (EuclideanSpace ℝ (Fin m))) i) *
        (F x j - (∫ y, F y ∂stdGaussian (EuclideanSpace ℝ (Fin m))) j)
          ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  rw [transport_mean hf0 hf hF hlaw]
  simpa only [mul_assoc] using (transport_integral hf0 hf hF hlaw
    (g := fun x => (x i - (∫ y, f y • y) i) * (x j - (∫ y, f y • y) j))
    (by fun_prop)).symm

end Submission.Obl.Entropy__gaussian_covariance_variational
