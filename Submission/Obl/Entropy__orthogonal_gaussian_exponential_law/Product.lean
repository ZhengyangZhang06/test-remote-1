import Submission.Obl.Entropy__orthogonal_gaussian_exponential_law.Scalar
import Submission.Obl.Entropy__affine_exponential_moments.Exponential
import Submission.Obl.Entropy__centered_slack_transports.Transport

open MeasureTheory ProbabilityTheory Set
open Submission.Obl.Entropy__affine_exponential_moments
open Submission.Obl.Entropy__centered_slack_transports

namespace Submission.Obl.Entropy__orthogonal_gaussian_exponential_law

lemma measurable_expDensity : Measurable expDensity :=
  (Real.continuous_exp.comp continuous_neg).measurable.indicator measurableSet_Ici

lemma expMeasure_eq_withDensity_expDensity :
    expMeasure 1 = volume.withDensity (fun x => ENNReal.ofReal (expDensity x)) := by
  change volume.withDensity (exponentialPDF 1) = _
  congr 1
  funext x
  rw [exponentialPDF_eq]
  simp [expDensity, Set.indicator, Set.mem_Ici]

lemma pi_expMeasure_eq_density (m : ℕ) :
    Measure.pi (fun _ : Fin m => expMeasure 1) =
      (volume : Measure (Fin m → ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i, expDensity (x i))) := by
  have : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  have hi : Integrable expDensity := by
    simpa using integrable_expDensity_pow 0
  have hpi : Integrable (fun x : Fin m → ℝ => ∏ i, expDensity (x i)) volume :=
    Integrable.fintype_prod (fun _ => hi)
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal hpi.integrableOn
      (ae_of_all _ (fun x => Finset.prod_nonneg (fun i _ => expDensity_nonneg (x i))))]
  change ENNReal.ofReal (∫ x, ∏ i, expDensity (x i)
    ∂(Measure.pi (fun _ : Fin m => (volume : Measure ℝ))).restrict (univ.pi s)) = _
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg expDensity_nonneg)]
  apply Finset.prod_congr rfl
  intro i _
  rw [expMeasure_eq_withDensity_expDensity, withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal hi.integrableOn
    (ae_of_all _ expDensity_nonneg)

lemma map_pi_expMeasure (m : ℕ) :
    (Measure.pi (fun _ : Fin m => expMeasure 1)).map (WithLp.toLp 2) =
      (volume : Measure (EuclideanSpace ℝ (Fin m))).withDensity
        (fun x => ENNReal.ofReal (productExpDensity x)) := by
  rw [pi_expMeasure_eq_density]
  change Measure.map (MeasurableEquiv.toLp 2 (Fin m → ℝ)) _ = _
  rw [map_withDensity_equiv]
  rw [show Measure.map (MeasurableEquiv.toLp 2 (Fin m → ℝ)) volume = volume from
    (PiLp.volume_preserving_toLp (Fin m)).map_eq]
  rfl

noncomputable def survivalMap {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => -Real.log (cdf (gaussianReal 0 1) (-x i)))

lemma continuous_survivalMap (m : ℕ) :
    Continuous (survivalMap : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) := by
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi (fun i => continuous_gaussian_survival.comp (by fun_prop))

/-- The coordinate transform sends the standard Gaussian to the exponential product density. -/
lemma map_survivalMap (m : ℕ) :
    (stdGaussian (EuclideanSpace ℝ (Fin m))).map survivalMap =
      volume.withDensity (fun x => ENNReal.ofReal (productExpDensity x)) := by
  rw [← map_pi_eq_stdGaussian,
    Measure.map_map (continuous_survivalMap m).measurable (by fun_prop)]
  have he : (survivalMap : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) ∘
      WithLp.toLp 2 = WithLp.toLp 2 ∘
        (fun x : Fin m → ℝ => fun i => -Real.log (cdf (gaussianReal 0 1) (-x i))) := rfl
  have hm : Measurable (fun x : Fin m → ℝ => fun i =>
      -Real.log (cdf (gaussianReal 0 1) (-x i))) :=
    measurable_pi_lambda _ (fun i =>
      continuous_gaussian_survival.measurable.comp (measurable_pi_apply i))
  rw [he, ← Measure.map_map (by fun_prop) hm]
  rw [Measure.pi_map_pi (fun _ => continuous_gaussian_survival.measurable.aemeasurable)]
  simp_rw [map_gaussian_survival]
  exact map_pi_expMeasure m

end Submission.Obl.Entropy__orthogonal_gaussian_exponential_law
