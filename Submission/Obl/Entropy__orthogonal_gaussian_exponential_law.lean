import Submission.Obl.Entropy__orthogonal_gaussian_exponential_law.Affine

set_option backward.isDefEq.respectTransparency false

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory
open Submission.Obl.Entropy__affine_exponential_moments
open Submission.Lib.EntropyTools
open Submission.Obl.Entropy__orthogonal_gaussian_exponential_law

theorem Submission.Entropy.orthogonal_gaussian_exponential_law : ∀ m : ℕ, 1 ≤ m → ∀ F : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), MeasureTheory.MemLp F 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) → MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) F = 0 → ∀ Q : (EuclideanSpace ℝ (Fin m)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin m)), ∀ a : (EuclideanSpace ℝ (Fin m)), (∀ x : (EuclideanSpace ℝ (Fin m)), ∀ i : Fin m, (Q.symm (F (Q x) - a)) i = -Real.log (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-x i))) → (MeasureTheory.Measure.map F (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))).withDensity (fun x => ENNReal.ofReal (|LinearMap.det Q.toLinearEquiv.toLinearMap|⁻¹ * (if ∀ i : Fin m, 0 ≤ Q.symm (x - a) i then Real.exp (-Finset.sum Finset.univ (fun i : Fin m => Q.symm (x - a) i)) else 0)))) ∧ ((fun i j => MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (fun x => F x i * F x j)) = (1 : (Matrix (Fin m) (Fin m) ℝ))) := by
  intro m hm F hLp hmean Q a hform
  have hF : F = fun x => Q (survivalMap (Q.symm x)) + a := by
    funext x
    have hv : Q.symm (F x - a) = survivalMap (Q.symm x) := by
      ext i
      change (Q.symm (F x - a)) i = -Real.log (cdf (gaussianReal 0 1) (-(Q.symm x) i))
      simpa only [Q.apply_symm_apply] using hform (Q.symm x) i
    have he := congrArg Q hv
    rw [Q.apply_symm_apply] at he
    exact sub_eq_iff_eq_add.mp he
  have hFc : Continuous F := by
    rw [hF]
    exact (Q.continuous.comp ((continuous_survivalMap m).comp Q.symm.continuous)).add
      continuous_const
  let d := affineDensity Q.toContinuousLinearEquiv a productExpDensity
  have hd0 : ∀ x, 0 ≤ d x :=
    affineDensity_nonneg _ _ productExpDensity_nonneg
  have hdi : Integrable d volume :=
    integrable_affineDensity _ _ (integrable_productExpDensity m)
  have hmap : (stdGaussian (EuclideanSpace ℝ (Fin m))).map F =
      volume.withDensity (fun x => ENNReal.ofReal (d x)) := by
    rw [hF]
    change Measure.map (((fun y => Q y + a) ∘ survivalMap) ∘ Q.symm) _ = _
    have hc : Measurable ((fun y => Q y + a) ∘
        (survivalMap : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))) :=
      ((Q.continuous.add continuous_const).comp (continuous_survivalMap m)).measurable
    rw [← Measure.map_map hc Q.symm.continuous.measurable, stdGaussian_map,
      ← Measure.map_map (by fun_prop) (continuous_survivalMap m).measurable,
      map_survivalMap, map_affine_density]
  constructor
  · simp only [d, affineDensity, productExpDensity_eq] at hmap
    convert! hmap using 1
  · have hmean_density : (∫ x, d x • x) = 0 := by
      rw [← integral_real_density hdi hd0 (fun x => x), ← hmap,
        integral_map hFc.measurable.aemeasurable (by fun_prop)]
      exact hmean
    have hc := covariance_orthogonal_product Q a
    change densityCovariance d (∫ x, d x • x) = 1 at hc
    rw [hmean_density] at hc
    ext i j
    have hi := integral_map (μ := stdGaussian (EuclideanSpace ℝ (Fin m)))
      hFc.measurable.aemeasurable
      (f := fun y : EuclideanSpace ℝ (Fin m) => y i * y j) (by fun_prop)
    rw [← hi, hmap, integral_real_density hdi hd0]
    simpa only [densityCovariance, PiLp.zero_apply, sub_zero, smul_eq_mul, mul_assoc]
      using congrFun (congrFun hc i) j
