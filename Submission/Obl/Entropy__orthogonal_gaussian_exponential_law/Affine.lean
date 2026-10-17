import Submission.Obl.Entropy__orthogonal_gaussian_exponential_law.Product

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set
open Submission.Obl.Entropy__affine_exponential_moments
open Submission.Obl.Entropy__centered_slack_transports
open Submission.Lib.EntropyTools

namespace Submission.Obl.Entropy__orthogonal_gaussian_exponential_law

lemma map_affine_density {m : ℕ}
    (Q : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m))
    (a : EuclideanSpace ℝ (Fin m)) (f : EuclideanSpace ℝ (Fin m) → ℝ) :
    Measure.map (fun x => Q x + a) (volume.withDensity (fun x => ENNReal.ofReal (f x))) =
      volume.withDensity (fun x =>
        ENNReal.ofReal (affineDensity Q.toContinuousLinearEquiv a f x)) := by
  have hlin := map_linear_density Q.toLinearEquiv f
  simp only [LinearIsometryEquiv.coe_toLinearEquiv] at hlin
  rw [show (fun x => Q x + a) = (fun x => x + a) ∘ Q from rfl,
    ← Measure.map_map (by fun_prop) Q.continuous.measurable,
    hlin]
  change Measure.map (Homeomorph.addRight a).toMeasurableEquiv _ = _
  rw [map_withDensity_equiv]
  rw [show Measure.map (Homeomorph.addRight a).toMeasurableEquiv volume = volume from
    map_add_right_eq_self volume a]
  rfl

lemma integral_real_density {X V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {μ : Measure X} {f : X → ℝ} (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (g : X → V) :
    (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) =
      ∫ x, f x • g x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hf.aemeasurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hf0 _)]

lemma linMatrix_isometry_mul_transpose {m : ℕ}
    (Q : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) :
    linMatrix Q.toContinuousLinearEquiv * (linMatrix Q.toContinuousLinearEquiv).transpose = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp
    (Q.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun (Fin m) ℝ)
      (EuclideanSpace.basisFun (Fin m) ℝ))
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  change linMatrix Q.toContinuousLinearEquiv *
    (linMatrix Q.toContinuousLinearEquiv).transpose = 1 at h
  exact h

lemma covariance_orthogonal_product {m : ℕ}
    (Q : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m))
    (a : EuclideanSpace ℝ (Fin m)) :
    densityCovariance (affineDensity Q.toContinuousLinearEquiv a productExpDensity)
      (∫ x, affineDensity Q.toContinuousLinearEquiv a productExpDensity x • x) = 1 := by
  rw [mean_affineDensity _ _ (integrable_productExpDensity m)
      (integrable_density_smul productExpDensity_nonneg (integrable_productExpDensity m)
        (integrable_second_productExpDensity m)) (integral_productExpDensity m),
    covariance_affineDensity _ _ _ productExpDensity_nonneg (integrable_productExpDensity m)
      (integrable_second_productExpDensity m),
    covariance_productExpDensity, Matrix.mul_one, linMatrix_isometry_mul_transpose]

end Submission.Obl.Entropy__orthogonal_gaussian_exponential_law
