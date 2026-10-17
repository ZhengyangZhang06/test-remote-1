import Submission.Obl.Entropy__transport_covariance_completion.GaussianDensity

namespace Submission.Obl.Entropy__transport_covariance_completion

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

variable {m : ℕ}

/-- The pointwise density equation follows from an injective C1 transport.
No surjectivity or continuity of the target density is needed. -/
theorem transport_density_equation_measurable
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hF : ContDiff ℝ 1 F) (hFinj : Function.Injective F)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hmap : Measure.map F (stdGaussian (EuclideanSpace ℝ (Fin m))) =
      volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      |(fderiv ℝ F x).det| * f (F x) = gaussianDensity x := by
  let D (x : EuclideanSpace ℝ (Fin m)) := |(fderiv ℝ F x).det|
  have hDm : Measurable D :=
    (ContinuousLinearMap.continuous_det.comp (hF.continuous_fderiv one_ne_zero)).abs.measurable
  have hEm := hF.continuous.measurableEmbedding hFinj
  have hfmF : Measurable (fun x => f (F x)) := hfm.comp hF.continuous.measurable
  have hJ : Measure.map F (volume.withDensity (fun x => ENNReal.ofReal (D x))) =
      volume.restrict (range F) := by
    simpa only [Measure.restrict_univ, image_univ] using
      map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure (EuclideanSpace ℝ (Fin m)))
        MeasurableSet.univ.nullMeasurableSet
        (fun x _ => (hF.differentiable one_ne_zero x).hasFDerivAt.hasFDerivWithinAt)
        hFinj.injOn
  have hmap' : Measure.map F
      (volume.withDensity (fun x => ENNReal.ofReal (D x * f (F x)))) =
      volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
    have he : (fun x => ENNReal.ofReal (D x * f (F x))) =
        (fun x => ENNReal.ofReal (D x)) * (fun x => ENNReal.ofReal (f (F x))) := by
      ext x
      exact ENNReal.ofReal_mul (abs_nonneg _)
    rw [he, withDensity_mul volume hDm.ennreal_ofReal
      hfmF.ennreal_ofReal,
      map_withDensity_comp hF.continuous.measurable hfm.ennreal_ofReal,
      hJ, ← restrict_withDensity hEm.measurableSet_range, ← hmap,
      Measure.restrict_map hF.continuous.measurable hEm.measurableSet_range,
      preimage_range, Measure.restrict_univ]
  have he := hEm.map_injective (hmap'.trans hmap.symm)
  rw [stdGaussian_eq_withDensity] at he
  have hae := (withDensity_eq_iff_of_sigmaFinite
    ((hDm.mul hfmF).ennreal_ofReal.aemeasurable)
    ((continuous_gaussianDensity m).measurable.ennreal_ofReal.aemeasurable)).mp he
  filter_upwards [hae] with x hx
  exact (ENNReal.ofReal_eq_ofReal_iff (mul_nonneg (abs_nonneg _) (hf0 _))
    (gaussianDensity_pos x).le).mp hx

/-- The density equation also holds for merely a.e. measurable target densities. -/
theorem transport_density_equation
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hF : ContDiff ℝ 1 F) (hFinj : Function.Injective F)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hfm : AEMeasurable f volume)
    (hf0 : ∀ x, 0 ≤ f x)
    (hmap : Measure.map F (stdGaussian (EuclideanSpace ℝ (Fin m))) =
      volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    ∀ᵐ x ∂stdGaussian (EuclideanSpace ℝ (Fin m)),
      |(fderiv ℝ F x).det| * f (F x) = gaussianDensity x := by
  let f' := fun x => max (hfm.mk f x) 0
  have hfm' : Measurable f' := hfm.measurable_mk.max measurable_const
  have hf0' : ∀ x, 0 ≤ f' x := fun x => le_max_right _ _
  have heq : f =ᵐ[volume] f' := by
    filter_upwards [hfm.ae_eq_mk] with x hx
    simp [f', ← hx, max_eq_left (hf0 x)]
  have hmap' : Measure.map F (stdGaussian (EuclideanSpace ℝ (Fin m))) =
      volume.withDensity (fun x => ENNReal.ofReal (f' x)) :=
    hmap.trans (withDensity_congr_ae (heq.fun_comp ENNReal.ofReal))
  have hg := transport_density_equation_measurable hF hFinj hfm' hf0' hmap'
  have hγac : stdGaussian (EuclideanSpace ℝ (Fin m)) ≪ volume := by
    rw [stdGaussian_eq_withDensity]
    exact withDensity_absolutelyContinuous _ _
  have hg' := hγac.ae_eq hg
  have ht : ∀ᵐ y ∂Measure.map F (stdGaussian (EuclideanSpace ℝ (Fin m))), f y = f' y := by
    rw [hmap]
    exact (withDensity_absolutelyContinuous _ _).ae_eq heq
  have ht' := ae_of_ae_map hF.continuous.measurable.aemeasurable ht
  filter_upwards [hg', ht'] with x hx he
  rwa [he]

/-- The logarithmic form of the transport density equation. -/
theorem transport_log_density
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hF : ContDiff ℝ 1 F) (hFinj : Function.Injective F)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hfm : AEMeasurable f volume)
    (hf0 : ∀ x, 0 ≤ f x)
    (hmap : Measure.map F (stdGaussian (EuclideanSpace ℝ (Fin m))) =
      volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    ∀ᵐ x ∂stdGaussian (EuclideanSpace ℝ (Fin m)),
      Real.log (f (F x)) = Real.log (gaussianDensity x) - Real.log |(fderiv ℝ F x).det| := by
  filter_upwards [transport_density_equation hF hFinj hfm hf0 hmap] with x hx
  have hprod : 0 < |(fderiv ℝ F x).det| * f (F x) := hx ▸ gaussianDensity_pos x
  have hdet : |(fderiv ℝ F x).det| ≠ 0 := by intro hz; simp [hz] at hprod
  have hf : f (F x) ≠ 0 := by intro hz; simp [hz] at hprod
  have hl := congrArg Real.log hx
  rw [Real.log_mul hdet hf] at hl
  linarith

/-- Entropy change of variables for the Gaussian source. -/
theorem entropy_change_of_variables
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hF : ContDiff ℝ 1 F) (hFinj : Function.Injective F)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : Integrable f volume)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfent : Integrable (fun x => f x * Real.log (f x)) volume)
    (hmap : Measure.map F (stdGaussian (EuclideanSpace ℝ (Fin m))) =
      volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    Integrable (fun x => Real.log |(fderiv ℝ F x).det|)
        (stdGaussian (EuclideanSpace ℝ (Fin m))) ∧
    (∫ x, f x * Real.log (f x)) =
      -(m : ℝ) * Real.log (2 * Real.pi) / 2 - (m : ℝ) / 2 -
        (∫ x, Real.log |(fderiv ℝ F x).det| ∂stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  have hfNN : AEMeasurable (fun x => (f x).toNNReal) volume :=
    measurable_real_toNNReal.comp_aemeasurable hf.aemeasurable
  have hlog : Integrable (fun x => Real.log (f x))
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) := by
    apply (integrable_withDensity_iff_integrable_smul₀ hfNN).mpr
    simpa only [NNReal.smul_def, Real.coe_toNNReal _ (hf0 _), smul_eq_mul] using hfent
  have hlogmap : Integrable (fun x => Real.log (f x))
      (Measure.map F (stdGaussian (EuclideanSpace ℝ (Fin m)))) := hmap ▸ hlog
  have hlogcomp : Integrable (fun x => Real.log (f (F x)))
      (stdGaussian (EuclideanSpace ℝ (Fin m))) :=
    hlogmap.comp_measurable hF.continuous.measurable
  have heq := transport_log_density hF hFinj hf.aemeasurable hf0 hmap
  have hdet : Integrable (fun x => Real.log |(fderiv ℝ F x).det|)
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
    refine ((integrable_log_gaussianDensity m).sub hlogcomp).congr ?_
    filter_upwards [heq] with x hx
    simp only [Pi.sub_apply]
    linarith
  refine ⟨hdet, ?_⟩
  have hi := integral_map hF.continuous.measurable.aemeasurable hlogmap.aestronglyMeasurable
  rw [hmap, integral_withDensity_eq_integral_toReal_smul₀ hf.aemeasurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hi
  simp only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul] at hi
  rw [hi, integral_congr_ae heq,
    integral_sub (integrable_log_gaussianDensity m) hdet,
    integral_log_gaussianDensity]

end Submission.Obl.Entropy__transport_covariance_completion
