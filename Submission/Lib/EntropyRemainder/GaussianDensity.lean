/-
Adapted from: here:o006

Original proofs by sessions x0016, x0019 and x0062.
-/

import Mathlib

/-!
# A Lebesgue density for the standard Gaussian on Euclidean space

The density representation lets the ordinary global integration-by-parts
formula apply to Gaussian expectations without separate boundary limits.
-/

namespace Submission.Lib.EntropyRemainder

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace

noncomputable def gaussianDensity {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ ^ m * Real.exp (-‖x‖ ^ 2 / 2)

lemma gaussianDensity_pos {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) :
    0 < gaussianDensity x := by
  unfold gaussianDensity
  positivity

lemma gaussianDensity_continuous {m : ℕ} :
    Continuous (gaussianDensity (m := m)) := by
  unfold gaussianDensity
  fun_prop

lemma gaussianDensity_contDiff {m : ℕ} {n : WithTop ℕ∞} :
    ContDiff ℝ n (gaussianDensity (m := m)) := by
  unfold gaussianDensity
  exact contDiff_const.mul (((contDiff_id.norm_sq ℝ).neg.div_const 2).exp)

lemma hasFDerivAt_gaussianDensity {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) :
    HasFDerivAt gaussianDensity (-(gaussianDensity x) • innerSL ℝ x) x := by
  have h := ((((hasStrictFDerivAt_norm_sq x).hasFDerivAt.neg).mul_const (1 / 2 : ℝ)).exp).const_mul
    ((Real.sqrt (2 * Real.pi))⁻¹ ^ m)
  convert! h using 1
  · ext y
    simp only [gaussianDensity, Pi.neg_apply, div_eq_mul_inv, one_mul]
  · ext v
    simp only [smul_apply, neg_apply, smul_eq_mul, innerSL_apply_apply,
      gaussianDensity, Pi.neg_apply, div_eq_mul_inv, one_mul]
    ring

lemma fderiv_gaussianDensity {m : ℕ} (x v : EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ gaussianDensity x v = -gaussianDensity x * inner ℝ x v := by
  rw [(hasFDerivAt_gaussianDensity x).fderiv]
  rfl

lemma gaussianDensity_eq_prod {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) :
    gaussianDensity x = ∏ i, gaussianPDFReal 0 1 (x i) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum, gaussianDensity, EuclideanSpace.real_norm_sq_eq,
    ← Finset.sum_div, ← Finset.sum_neg_distrib]

lemma gaussian_pi_eq_withDensity (m : ℕ) :
    Measure.pi (fun _ : Fin m => gaussianReal 0 1) =
      volume.withDensity (fun x : Fin m → ℝ =>
        ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    show (volume : Measure (Fin m → ℝ)) = Measure.pi (fun _ => volume) from rfl,
    Measure.restrict_pi_pi]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod (fun _ => (integrable_gaussianPDFReal 0 1).integrableOn))
    (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun i _ =>
      gaussianPDFReal_nonneg 0 1 (x i)), integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg fun x =>
      gaussianPDFReal_nonneg 0 1 x)]
  apply Finset.prod_congr rfl
  intro i _
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, withDensity_apply _ (hs i),
    ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal 0 1).integrableOn
      (Filter.Eventually.of_forall fun x => gaussianPDFReal_nonneg 0 1 x)]
  rfl

lemma stdGaussian_eq_withDensity (m : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin m)) =
      volume.withDensity (fun x => ENNReal.ofReal (gaussianDensity x)) := by
  rw [← map_pi_eq_stdGaussian, gaussian_pi_eq_withDensity]
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (by fun_prop) hs,
    withDensity_apply _ ((by fun_prop : Measurable (@WithLp.toLp 2 (Fin m → ℝ))) hs),
    withDensity_apply _ hs]
  simpa only [gaussianDensity_eq_prod] using
    (PiLp.volume_preserving_toLp (Fin m)).setLIntegral_comp_preimage hs
      (gaussianDensity_continuous.measurable.ennreal_ofReal)

lemma gaussian_integrable_iff {m : ℕ} {f : EuclideanSpace ℝ (Fin m) → ℝ} :
    Integrable f (stdGaussian (EuclideanSpace ℝ (Fin m))) ↔
      Integrable (fun x => gaussianDensity x * f x) := by
  rw [stdGaussian_eq_withDensity, integrable_withDensity_iff_integrable_smul'
    (gaussianDensity_continuous.measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (gaussianDensity_pos _).le, smul_eq_mul]

lemma gaussian_integral_eq {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ) :
    (∫ x, f x ∂stdGaussian (EuclideanSpace ℝ (Fin m))) =
      ∫ x, gaussianDensity x * f x := by
  rw [stdGaussian_eq_withDensity, integral_withDensity_eq_integral_toReal_smul
    (gaussianDensity_continuous.measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (gaussianDensity_pos _).le, smul_eq_mul]

end Submission.Lib.EntropyRemainder
