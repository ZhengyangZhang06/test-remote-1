import Mathlib.Probability.CDF
import Submission.Obl.Entropy__gaussian_hazard_lipschitz.GaussianMoments

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace Submission.Obl.Entropy__gaussian_hazard_lipschitz

noncomputable def mass (a : ℝ) : ℝ := ∫ x in Iic a, pdf x

lemma cdf_eq_mass (a : ℝ) : cdf (gaussianReal 0 1) a = mass a := by
  rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero]
  exact ENNReal.toReal_ofReal (integral_nonneg (fun x => (pdf_pos x).le))

lemma mass_pos (a : ℝ) : 0 < mass a := by
  have hs : Function.support pdf = univ := by
    ext x
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (pdf_pos x).ne'
  rw [mass, setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => (pdf_pos x).le)) integrable_pdf.integrableOn]
  simp [hs]

lemma hasDerivAt_mass (a : ℝ) : HasDerivAt mass (pdf a) a := by
  have he : mass = fun b => (∫ x in (0 : ℝ)..b, pdf x) + mass 0 := by
    ext b
    exact sub_eq_iff_eq_add.mp (intervalIntegral.integral_Iic_sub_Iic
      integrable_pdf.integrableOn integrable_pdf.integrableOn)
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right
    (continuous_pdf.intervalIntegrable _ _)
    continuous_pdf.stronglyMeasurable.stronglyMeasurableAtFilter
    continuous_pdf.continuousAt).add_const _

lemma mean_le_endpoint (a : ℝ) : 0 ≤ a * mass a + pdf a := by
  have hi : Integrable (fun x : ℝ => x * pdf x) := by
    simpa only [pow_one] using integrable_pow_mul_pdf 1
  have h := setIntegral_mono_on hi.integrableOn
    (integrable_pdf.const_mul a).integrableOn measurableSet_Iic
    (fun x hx => mul_le_mul_of_nonneg_right hx (pdf_pos x).le)
  rw [integral_first_moment, integral_const_mul] at h
  change -pdf a ≤ a * mass a at h
  linarith

lemma shifted_second_moment_nonneg (a c : ℝ) :
    0 ≤ mass a - a * pdf a - 2 * c * pdf a + c ^ 2 * mass a := by
  have hi : Integrable (fun x : ℝ => x * pdf x) := by
    simpa only [pow_one] using integrable_pow_mul_pdf 1
  have he : (fun x : ℝ => (x + c) ^ 2 * pdf x) =
      (fun x => x ^ 2 * pdf x + (2 * c) * (x * pdf x) + c ^ 2 * pdf x) := by
    ext x
    ring
  have hn : 0 ≤ ∫ x in Iic a, (x + c) ^ 2 * pdf x :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (pdf_pos x).le)
  have hi2 : Integrable (fun x : ℝ => x ^ 2 * pdf x + (2 * c) * (x * pdf x)) :=
    (integrable_pow_mul_pdf 2).add (hi.const_mul (2 * c))
  rw [he, integral_add
    hi2.integrableOn
    (integrable_pdf.const_mul (c ^ 2)).integrableOn,
    integral_add (integrable_pow_mul_pdf 2).integrableOn
    (hi.const_mul (2 * c)).integrableOn,
    integral_const_mul, integral_const_mul, integral_first_moment,
    integral_second_moment] at hn
  change 0 ≤ mass a - a * pdf a + 2 * c * -pdf a + c ^ 2 * mass a at hn
  nlinarith

end Submission.Obl.Entropy__gaussian_hazard_lipschitz
