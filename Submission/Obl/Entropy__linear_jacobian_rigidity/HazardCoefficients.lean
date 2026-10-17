import Mathlib
import Submission.Obl.Entropy__gaussian_hazard_lipschitz.Hazard

/-! Scalar regularity and nonvanishing Taylor coefficients needed by Lemma 6.1. -/

namespace Submission.Obl.Entropy__linear_jacobian_rigidity

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

open Submission.Obl.Entropy__gaussian_hazard_lipschitz

lemma hazard_contDiff_two : ContDiff ℝ 2 hazard := by
  have hd : Differentiable ℝ hazard := fun x ↦ (hasDerivAt_hazard x).differentiableAt
  have he : deriv hazard = fun x ↦ hazard x * (hazard x - x) :=
    funext fun x ↦ (hasDerivAt_hazard x).deriv
  have hc : ContDiff ℝ 1 hazard := by
    rw [contDiff_one_iff_deriv, he]
    exact ⟨hd, hd.continuous.mul (hd.continuous.sub continuous_id)⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv, he]
  exact ⟨hd, by simp, hc.mul (hc.sub contDiff_id)⟩

lemma hazard_first_coefficient_pos : 0 < deriv hazard 0 := by
  rw [(hasDerivAt_hazard 0).deriv, sub_zero]
  have hp : 0 < hazard 0 := div_pos (pdf_pos 0) (mass_pos (-0))
  exact mul_pos hp hp

lemma hazard_second_derivative (x : ℝ) :
    deriv (deriv hazard) x =
      hazard x * (hazard x - x) * (hazard x - x) +
        hazard x * (hazard x * (hazard x - x) - 1) := by
  have he : deriv hazard = fun x ↦ hazard x * (hazard x - x) :=
    funext fun x ↦ (hasDerivAt_hazard x).deriv
  rw [he]
  exact ((hasDerivAt_hazard x).mul ((hasDerivAt_hazard x).sub (hasDerivAt_id x))).deriv

lemma gaussian_mass_zero : mass 0 = (1 / 2 : ℝ) := by
  have he : (∫ x in Ioi (0 : ℝ), pdf x) = mass 0 := by
    simpa only [pdf_neg, neg_zero, mass] using (integral_comp_neg_Iic 0 pdf).symm
  have hi := integral_add_compl (f := pdf) (s := Iic (0 : ℝ)) measurableSet_Iic integrable_pdf
  rw [compl_Iic, he] at hi
  have hone : (∫ x, pdf x) = 1 := integral_gaussianPDFReal_eq_one 0 one_ne_zero
  rw [hone] at hi
  change mass 0 + mass 0 = 1 at hi
  linarith

lemma hazard_zero_sq : hazard 0 ^ 2 = 2 / Real.pi := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hs : (Real.sqrt (2 * Real.pi)) ^ 2 = 2 * Real.pi :=
    Real.sq_sqrt (by positivity)
  have hs0 : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  rw [hazard, neg_zero, gaussian_mass_zero, pdf_formula]
  norm_num
  field_simp
  rw [Real.sq_sqrt hp.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

lemma hazard_second_coefficient_pos : 0 < deriv (deriv hazard) 0 := by
  have hp : 0 < hazard 0 := div_pos (pdf_pos 0) (mass_pos (-0))
  have hs : (1 / 2 : ℝ) < hazard 0 ^ 2 := by
    rw [hazard_zero_sq]
    apply (lt_div_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_lt_four]
  have hpos : 0 < hazard 0 * (2 * hazard 0 ^ 2 - 1) := by
    apply mul_pos hp
    linarith
  rw [hazard_second_derivative]
  nlinarith

/-- The exact scalar function in the frozen Jacobian is C², with both
nonconstant Taylor coefficients nonzero. -/
theorem gaussian_hazard_coefficients :
    let q : ℝ → ℝ := fun t ↦ gaussianPDFReal 0 1 t / cdf (gaussianReal 0 1) (-t)
    ContDiff ℝ 2 q ∧ deriv q 0 ≠ 0 ∧ deriv (deriv q) 0 ≠ 0 := by
  have he : (fun t ↦ gaussianPDFReal 0 1 t / cdf (gaussianReal 0 1) (-t)) = hazard := by
    funext t
    rw [cdf_eq_mass]
    rfl
  dsimp only
  rw [he]
  exact ⟨hazard_contDiff_two, hazard_first_coefficient_pos.ne', hazard_second_coefficient_pos.ne'⟩

end Submission.Obl.Entropy__linear_jacobian_rigidity
