import Submission.Lib.EntropyTools.DensityMoments

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Submission.Obl.Entropy__centered_slack_transports

variable {m : ℕ}

/-- A measurable change of coordinates transports an arbitrary density. -/
theorem map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (w : α → ℝ≥0∞) :
    Measure.map e (μ.withDensity w) =
      (Measure.map e μ).withDensity (fun x => w (e.symm x)) := by
  apply Measure.ext
  intro s hs
  rw [e.measurableEmbedding.map_apply, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, ← lintegral_indicator hs, lintegral_map_equiv,
    ← lintegral_indicator (e.measurable hs)]
  apply lintegral_congr
  intro x
  by_cases hx : e x ∈ s <;> simp [hx]

/-- The determinant density formula is exactly the law of a linear image. -/
theorem map_linear_density
    (P : EuclideanSpace ℝ (Fin m) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (Fin m) → ℝ) :
    Measure.map P (volume.withDensity (fun x => ENNReal.ofReal (f x))) =
      volume.withDensity (fun x => ENNReal.ofReal
        (|LinearMap.det P.toLinearMap|⁻¹ * f (P.symm x))) := by
  let e := P.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : (e : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) = P := by
    simp [e]
  rw [← he, map_withDensity_equiv, he]
  have hdet : LinearMap.det P.toLinearMap ≠ 0 := by
    exact P.isUnit_det'.ne_zero
  have hmap : Measure.map P volume = ENNReal.ofReal |(LinearMap.det P.toLinearMap)⁻¹| • volume := by
    change Measure.map P.toLinearMap volume = _
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet
  rw [hmap, withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext x
  simp [e, ENNReal.ofReal_mul (inv_nonneg.mpr (abs_nonneg _)), abs_inv]

/-- A Gaussian transport of a linear image of a density with a finite second moment
can be centered, without changing its derivative. -/
theorem center_transport
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2) volume)
    (P : EuclideanSpace ℝ (Fin m) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hG : ContDiff ℝ 1 G)
    (hlaw : Measure.map G (stdGaussian (EuclideanSpace ℝ (Fin m))) =
      Measure.map P (volume.withDensity (fun x => ENNReal.ofReal (f x)))) :
    ∃ F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m),
      (ContDiff ℝ 1 F ∧ MemLp F 2 (stdGaussian (EuclideanSpace ℝ (Fin m))) ∧
        ∫ x, F x ∂stdGaussian (EuclideanSpace ℝ (Fin m)) = 0) ∧
      Measure.map F (stdGaussian (EuclideanSpace ℝ (Fin m))) =
        Measure.map (fun x => P (x - ∫ y, f y • y))
          (volume.withDensity (fun x => ENNReal.ofReal (f x))) ∧
      ∀ x, fderiv ℝ F x = fderiv ℝ G x := by
  let ν := volume.withDensity (fun x => ENNReal.ofReal (f x))
  let γ := stdGaussian (EuclideanSpace ℝ (Fin m))
  let L := P.toContinuousLinearEquiv.toContinuousLinearMap
  let b := ∫ y, f y • y
  have hPc : Continuous P := P.toContinuousLinearEquiv.continuous
  have hid : MemLp (id : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) 2 ν := by
    apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
    apply (integrable_withDensity_iff_integrable_smul₀'
      hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal (by simp)).2
    simpa only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul, id_eq] using hf2
  have hP : MemLp P 2 ν := hid.continuousLinearMap_comp L
  have hGlp : MemLp G 2 γ := by
    have hidP : MemLp (id : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
        2 (Measure.map P ν) :=
      (memLp_map_measure_iff continuous_id.aestronglyMeasurable hPc.measurable.aemeasurable).2 hP
    rw [← hlaw] at hidP
    exact (memLp_map_measure_iff continuous_id.aestronglyMeasurable
      hG.continuous.measurable.aemeasurable).1 hidP
  have hmean : ∫ x, G x ∂γ = P b := by
    calc
      ∫ x, G x ∂γ = ∫ x, id x ∂Measure.map G γ :=
        (integral_map hG.continuous.measurable.aemeasurable
          continuous_id.aestronglyMeasurable).symm
      _ = ∫ x, id x ∂Measure.map P ν := by rw [hlaw]
      _ = ∫ x, P x ∂ν := integral_map hPc.measurable.aemeasurable
        continuous_id.aestronglyMeasurable
      _ = ∫ x, f x • P x := by
        rw [integral_withDensity_eq_integral_toReal_smul₀
          hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal (by simp)]
        simp only [ENNReal.toReal_ofReal (hf0 _)]
      _ = P b := by
        simpa [L, b] using L.integral_comp_comm
          (Submission.Lib.EntropyTools.integrable_density_smul hf0 hf hf2)
  refine ⟨fun x => G x - P b, ⟨hG.sub contDiff_const, hGlp.sub (memLp_const _), ?_⟩, ?_, ?_⟩
  · rw [integral_sub (hGlp.integrable (by norm_num)) (integrable_const _), hmean]
    simp [γ]
  · have h := congrArg (Measure.map (fun x => x - P b)) hlaw
    rw [Measure.map_map (by fun_prop) hG.continuous.measurable,
      Measure.map_map (by fun_prop) hPc.measurable] at h
    simpa only [Function.comp_def, map_sub] using h
  · intro x
    exact fderiv_sub_const _

end Submission.Obl.Entropy__centered_slack_transports
