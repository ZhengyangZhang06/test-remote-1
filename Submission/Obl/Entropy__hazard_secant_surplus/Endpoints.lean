import Submission.Lib.GaussianTransport.GaussianSlope

open MeasureTheory Set

namespace Submission.Obl.Entropy__hazard_secant_surplus

open Submission.Lib.GaussianTransport

lemma normalPDF_formula (x : ℝ) :
    normalPDF x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
  simp only [normalPDF, ProbabilityTheory.gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
    neg_div]

lemma normalPDF_zero_bounds : (79 / 200 : ℝ) ≤ normalPDF 0 ∧ normalPDF 0 ≤ 2 / 5 := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have he := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  rw [normalPDF_formula]
  norm_num only [zero_pow (by decide : 2 ≠ 0), zero_div, neg_zero, Real.exp_zero, mul_one]
  rw [← one_div]
  constructor
  · apply (le_div_iff₀ hs).mpr
    nlinarith [Real.pi_lt_d2, sq_nonneg (Real.sqrt (2 * Real.pi) - 200 / 79)]
  · apply (div_le_iff₀ hs).mpr
    nlinarith [Real.pi_gt_d2]

lemma normalPDF_eq_zero_mul (x : ℝ) :
    normalPDF x = normalPDF 0 * Real.exp (-(x ^ 2 / 2)) := by
  rw [normalPDF_formula x, normalPDF_formula 0]
  norm_num

lemma normalCDF_one_lower : (199 / 240 : ℝ) ≤ normalCDF 1 := by
  have hi : (∫ x in (0 : ℝ)..1, normalPDF x) = normalCDF 1 - normalCDF 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_normalCDF x)
      (contDiff_normalPDF.continuous.intervalIntegrable 0 1)
  have hp : (∫ x in (0 : ℝ)..1, 1 - x ^ 2 / 2) = 5 / 6 := by
    have h1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 := continuous_const.intervalIntegrable 0 1
    have h2 : IntervalIntegrable (fun x : ℝ => x ^ 2 / 2) volume 0 1 :=
      ((continuous_id.pow 2).div_const 2).intervalIntegrable 0 1
    rw [intervalIntegral.integral_sub h1 h2,
      intervalIntegral.integral_const, intervalIntegral.integral_div, integral_pow]
    norm_num
  have h := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    ((continuous_const.mul (continuous_const.sub ((continuous_id.pow 2).div_const 2))).intervalIntegrable 0 1)
    (contDiff_normalPDF.continuous.intervalIntegrable 0 1)
    (f := fun x => normalPDF 0 * (1 - x ^ 2 / 2)) (g := normalPDF) ?_
  · rw [intervalIntegral.integral_const_mul, hp, hi, normalCDF_zero] at h
    nlinarith [normalPDF_zero_bounds.1]
  · intro x _
    rw [normalPDF_eq_zero_mul x]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (-(x ^ 2 / 2))])
      (normalPDF_pos 0).le

lemma exp_half_lower : (100 / 61 : ℝ) ≤ Real.exp (1 / 2) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

lemma exp_two_lower : (22 / 3 : ℝ) ≤ Real.exp 2 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

lemma exp_nine_halves_lower : (80 : ℝ) ≤ Real.exp (9 / 2) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 2) 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

lemma gaussianHazard_neg_one_le : gaussianHazard (-1) ≤ 59 / 200 := by
  have hp : normalPDF (-1) ≤ (2 / 5 : ℝ) * (61 / 100) := by
    rw [normalPDF_eq_zero_mul (-1), show -((-1 : ℝ) ^ 2 / 2) = -(1 / 2) by norm_num, Real.exp_neg]
    have he : (Real.exp (1 / 2))⁻¹ ≤ 61 / 100 := by
      rw [← one_div]
      apply (div_le_iff₀ (Real.exp_pos _)).mpr
      nlinarith [exp_half_lower]
    exact mul_le_mul normalPDF_zero_bounds.2 he (by positivity) (by norm_num)
  unfold gaussianHazard
  norm_num only [neg_neg]
  apply (div_le_iff₀ (normalCDF_pos 1)).mpr
  nlinarith [normalCDF_one_lower]

lemma gaussianHazard_neg_two_le : gaussianHazard (-2) ≤ 1 / 15 := by
  have hp : normalPDF (-2) ≤ (2 / 5 : ℝ) * (3 / 22) := by
    rw [normalPDF_eq_zero_mul (-2), show -((-2 : ℝ) ^ 2 / 2) = -2 by norm_num, Real.exp_neg]
    have he : (Real.exp 2)⁻¹ ≤ 3 / 22 := by
      rw [← one_div]
      apply (div_le_iff₀ (Real.exp_pos _)).mpr
      nlinarith [exp_two_lower]
    exact mul_le_mul normalPDF_zero_bounds.2 he (by positivity) (by norm_num)
  have hc : (199 / 240 : ℝ) ≤ normalCDF 2 := normalCDF_one_lower.trans
    (ProbabilityTheory.monotone_cdf _ (by norm_num : (1 : ℝ) ≤ 2))
  unfold gaussianHazard
  norm_num only [neg_neg]
  apply (div_le_iff₀ (normalCDF_pos 2)).mpr
  nlinarith

lemma gaussianHazard_neg_three_le : gaussianHazard (-3) ≤ 1 / 100 := by
  have hp : normalPDF (-3) ≤ (2 / 5 : ℝ) * (1 / 80) := by
    rw [normalPDF_eq_zero_mul (-3), show -((-3 : ℝ) ^ 2 / 2) = -(9 / 2) by norm_num, Real.exp_neg]
    have he : (Real.exp (9 / 2))⁻¹ ≤ 1 / 80 := by
      rw [← one_div]
      apply (div_le_iff₀ (Real.exp_pos _)).mpr
      nlinarith [exp_nine_halves_lower]
    exact mul_le_mul normalPDF_zero_bounds.2 he (by positivity) (by norm_num)
  have hc : (1 / 2 : ℝ) ≤ normalCDF 3 := by
    rw [← normalCDF_zero]
    exact ProbabilityTheory.monotone_cdf _ (by norm_num : (0 : ℝ) ≤ 3)
  unfold gaussianHazard
  norm_num only [neg_neg]
  apply (div_le_iff₀ (normalCDF_pos 3)).mpr
  nlinarith

end Submission.Obl.Entropy__hazard_secant_surplus
