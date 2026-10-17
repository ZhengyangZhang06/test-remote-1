import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace Submission.Obl.Entropy__gaussian_hazard_lipschitz

noncomputable def pdf (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

lemma pdf_formula (x : ℝ) :
    pdf x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
  simp only [pdf, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  congr 2
  ring

lemma pdf_pos (x : ℝ) : 0 < pdf x :=
  gaussianPDFReal_pos 0 1 x one_ne_zero

lemma pdf_neg (x : ℝ) : pdf (-x) = pdf x := by
  simp only [pdf_formula, neg_sq]

lemma hasDerivAt_pdf (x : ℝ) : HasDerivAt pdf (-x * pdf x) x := by
  have h := (((hasDerivAt_id x).pow 2).const_mul (-(1 / 2 : ℝ))).exp.const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert! h using 1
  · ext t
    exact pdf_formula t
  · rw [pdf_formula]
    simp only [Pi.pow_apply, id_eq]
    ring

lemma continuous_pdf : Continuous pdf :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_pdf x).continuousAt)

lemma integrable_pdf : Integrable pdf := integrable_gaussianPDFReal 0 1

lemma integrable_pow_mul_pdf (n : ℕ) : Integrable (fun x : ℝ => x ^ n * pdf x) := by
  have h := (integrable_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ))
    (by norm_num) (s := (n : ℝ)) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  convert! h using 1
  ext x
  rw [Real.rpow_natCast, pdf_formula]
  ring

lemma integral_first_moment (a : ℝ) :
    (∫ x in Iic a, x * pdf x) = -pdf a := by
  have hi : Integrable (fun x : ℝ => x * pdf x) := by
    simpa only [pow_one] using integrable_pow_mul_pdf 1
  have hd (x : ℝ) : HasDerivAt (fun x => -pdf x) (x * pdf x) x := by
    simpa only [neg_mul, neg_neg] using! (hasDerivAt_pdf x).neg
  have ht := tendsto_zero_of_hasDerivAt_of_integrableOn_Iic
    (a := a) (fun x _ => hd x) hi.integrableOn integrable_pdf.neg.integrableOn
  simpa only [sub_zero] using
    integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hd x) hi.integrableOn ht

lemma integral_second_moment (a : ℝ) :
    (∫ x in Iic a, x ^ 2 * pdf x) = (∫ x in Iic a, pdf x) - a * pdf a := by
  have hi : Integrable (fun x : ℝ => x * pdf x) := by
    simpa only [pow_one] using integrable_pow_mul_pdf 1
  have hd (x : ℝ) :
      HasDerivAt (fun x => x * pdf x) (pdf x - x ^ 2 * pdf x) x := by
    convert! (hasDerivAt_id x).mul (hasDerivAt_pdf x) using 1
    simp only [id_eq]
    ring
  have hi' := integrable_pdf.sub (integrable_pow_mul_pdf 2)
  have ht := tendsto_zero_of_hasDerivAt_of_integrableOn_Iic
    (a := a) (fun x _ => hd x) hi'.integrableOn hi.integrableOn
  have he := integral_Iic_of_hasDerivAt_of_tendsto' (a := a)
    (fun x _ => hd x) hi'.integrableOn ht
  rw [integral_sub integrable_pdf.integrableOn (integrable_pow_mul_pdf 2).integrableOn,
    sub_zero] at he
  linarith

end Submission.Obl.Entropy__gaussian_hazard_lipschitz
