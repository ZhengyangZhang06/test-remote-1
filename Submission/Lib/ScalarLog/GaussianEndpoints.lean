/-
Adapted from: here:root
Original exact endpoint and logarithmic separation proofs by session x0023.
-/

import Submission.Lib.GaussianTransport.GaussianTails

/-! Exact rational endpoint bounds used in Section 4.2 of the supplied paper. -/

open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace Submission.Lib.ScalarLog

open Submission.Lib.GaussianTransport

theorem normalPDF_eq_inv (a : ℝ) :
    normalPDF a = 1 / (Real.sqrt (2 * Real.pi) * Real.exp (a ^ 2 / 2)) := by
  simp only [normalPDF, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  rw [neg_div, Real.exp_neg, one_div, mul_inv_rev]
  ring

theorem sqrt_two_pi_lower : (5 : ℝ) / 2 < Real.sqrt (2 * Real.pi) := by
  have hp := Real.pi_gt_d2
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)
  have hn := Real.sqrt_nonneg (2 * Real.pi)
  nlinarith

private theorem sqrt_two_pi_upper : Real.sqrt (2 * Real.pi) < (251 : ℝ) / 100 := by
  have hp := Real.pi_lt_d2
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)
  have hn := Real.sqrt_nonneg (2 * Real.pi)
  nlinarith

private theorem normalPDF_two_lt : normalPDF 2 < (34 : ℝ) / 625 := by
  have he : (2718 : ℝ) / 1000 < Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have he2 : (2718 / 1000 : ℝ) ^ 2 < Real.exp 2 := by
    have h : Real.exp 2 = Real.exp 1 ^ 2 := by
      norm_num [← Real.exp_nat_mul]
    rw [h]
    nlinarith [Real.exp_pos 1]
  rw [normalPDF_eq_inv, show (2 : ℝ) ^ 2 / 2 = 2 by norm_num]
  apply (div_lt_iff₀ (mul_pos (Real.sqrt_pos.2 (by positivity)) (Real.exp_pos 2))).2
  nlinarith [mul_lt_mul_of_pos_left he2 (lt_trans (by norm_num) sqrt_two_pi_lower),
    mul_lt_mul_of_pos_right sqrt_two_pi_lower (by norm_num : (0 : ℝ) < (2718 / 1000) ^ 2)]

private theorem normalPDF_three_lt : normalPDF 3 < (1 : ℝ) / 204 := by
  have he : (27 : ℝ) / 10 < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he9 : (27 / 10 : ℝ) ^ 9 < Real.exp 9 := by
    have h : Real.exp 9 = Real.exp 1 ^ 9 := by
      norm_num [← Real.exp_nat_mul]
    rw [h]
    exact pow_lt_pow_left₀ he (by norm_num) (by norm_num)
  have hehalf : (85 : ℝ) < Real.exp (9 / 2) := by
    have hsq : Real.exp (9 / 2) ^ 2 = Real.exp 9 := by
      rw [pow_two, ← Real.exp_add]
      norm_num
    nlinarith [Real.exp_pos (9 / 2)]
  rw [normalPDF_eq_inv, show (3 : ℝ) ^ 2 / 2 = 9 / 2 by norm_num]
  apply (div_lt_iff₀ (mul_pos (Real.sqrt_pos.2 (by positivity)) (Real.exp_pos (9 / 2)))).2
  nlinarith [mul_lt_mul_of_pos_left hehalf (lt_trans (by norm_num) sqrt_two_pi_lower),
    mul_lt_mul_of_pos_right sqrt_two_pi_lower (by norm_num : (0 : ℝ) < 85)]

/-- The endpoint at `-3`, with the paper's constant `0.005`. -/
theorem gaussianHazard_neg_three_lt : gaussianHazard (-3) < (1 : ℝ) / 200 := by
  have hm := normalPDF_sub_mul_normalCDF_pos 3
  have hr := normalCDF_add_neg 3
  have hp := normalPDF_three_lt
  unfold gaussianHazard
  rw [normalPDF_neg]
  norm_num only [neg_neg]
  apply (div_lt_iff₀ (normalCDF_pos 3)).2
  linarith

/-- The endpoint at `-2`, with the paper's constant `0.056`. -/
theorem gaussianHazard_neg_two_lt : gaussianHazard (-2) < (7 : ℝ) / 125 := by
  have hm := normalPDF_sub_mul_normalCDF_pos 2
  have hr := normalCDF_add_neg 2
  have hp := normalPDF_two_lt
  unfold gaussianHazard
  rw [normalPDF_neg]
  norm_num only [neg_neg]
  apply (div_lt_iff₀ (normalCDF_pos 2)).2
  linarith

/-- The positive endpoint follows from the strict Mills inequality. -/
theorem gaussianHazard_four_gt : (4 : ℝ) < gaussianHazard 4 := by
  exact sub_pos.mp (gaussianGap_pos 4)

private theorem exp_neg_half_gt : (20 : ℝ) / 33 < Real.exp (-1 / 2) := by
  have he : Real.exp (1 / 2) < (33 : ℝ) / 20 := by
    have hs : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [pow_two, ← Real.exp_add]
      norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 / 2)]
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.exp_neg]
  rw [lt_inv_comm₀ (by norm_num) (Real.exp_pos _)]
  norm_num
  exact he

private theorem exp_neg_sq_upper (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    Real.exp (-x ^ 2 / 2) ≤
      1 - x ^ 2 / 2 + x ^ 4 / 8 - x ^ 6 / 48 + x ^ 8 / 384 + 1 / 3200 := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  have habs : |-x ^ 2 / 2| ≤ (1 : ℝ) / 2 := by
    rw [abs_of_nonpos (by nlinarith [sq_nonneg x] : -x ^ 2 / 2 ≤ 0)]
    nlinarith [sq_nonneg x]
  have h := Real.exp_bound (habs.trans (by norm_num)) (show 0 < 5 by decide)
  have hh := (abs_sub_le_iff.mp h).1
  have hp : |-x ^ 2 / 2| ^ 5 ≤ ((1 : ℝ) / 2) ^ 5 := by gcongr
  norm_num [Finset.sum_range_succ] at hh
  nlinarith [hp]

private theorem integral_exp_neg_sq_upper :
    (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2 / 2)) < 107 / 125 := by
  let P : ℝ → ℝ := fun x =>
    1 - x ^ 2 / 2 + x ^ 4 / 8 - x ^ 6 / 48 + x ^ 8 / 384 + 1 / 3200
  have hp : Continuous P := by fun_prop
  have he : Continuous (fun x : ℝ => Real.exp (-x ^ 2 / 2)) := by fun_prop
  have hle := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (he.intervalIntegrable 0 1) (hp.intervalIntegrable 0 1) exp_neg_sq_upper
  have hval : (∫ x in (0 : ℝ)..1, P x) =
      1 - 1 / 6 + 1 / 40 - 1 / 336 + 1 / 3456 + 1 / 3200 := by
    dsimp [P]
    simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
      [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_div, intervalIntegral.integral_const,
      integral_pow, smul_eq_mul]
    norm_num
  rw [hval] at hle
  exact hle.trans_lt (by norm_num)

/-- The endpoint at `-1`, with the paper's constant `0.287`. -/
theorem gaussianHazard_neg_one_gt : (287 : ℝ) / 1000 < gaussianHazard (-1) := by
  let c : ℝ := Real.sqrt (2 * Real.pi)
  let A : ℝ := ∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2 / 2)
  have hc : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hpdf : c * normalPDF 1 = Real.exp (-1 / 2) := by
    dsimp [c, normalPDF, gaussianPDFReal]
    norm_num only [NNReal.coe_one, sub_zero, mul_one, one_pow]
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul]
  have hid : (∫ x in (0 : ℝ)..1, normalPDF x) = c⁻¹ * A := by
    simp only [normalPDF, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
    exact intervalIntegral.integral_const_mul _ _
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_normalCDF x) (contDiff_normalPDF.continuous.intervalIntegrable 0 1)
      (a := (0 : ℝ)) (b := 1)
  rw [hid, normalCDF_zero] at hi
  have hcdf : c * normalCDF 1 = c / 2 + A := by
    have h' := congrArg (fun z : ℝ => c * z) hi
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul] at h'
    linarith
  have hu : c / 2 + A < (2111 : ℝ) / 1000 := by
    have hs := sqrt_two_pi_upper
    have ha := integral_exp_neg_sq_upper
    dsimp [c, A] at *
    linarith
  have hcomp : (287 / 1000 : ℝ) * normalCDF 1 < normalPDF 1 := by
    have hn := exp_neg_half_gt
    rw [← hpdf] at hn
    rw [← hcdf] at hu
    nlinarith
  unfold gaussianHazard
  rw [normalPDF_neg]
  norm_num only [neg_neg]
  exact (lt_div_iff₀ (normalCDF_pos 1)).2 hcomp

/-- The logarithmic separation between `-2` and `-1`. -/
theorem log_hazard_neg_one_sub_neg_two_gt :
    (81 : ℝ) / 50 < Real.log (gaussianHazard (-1)) - Real.log (gaussianHazard (-2)) := by
  have h := Real.sum_range_le_log_div (x := (231 / 343 : ℝ)) (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h
  have hratio : Real.log (41 / 8 : ℝ) =
      Real.log (287 / 1000 : ℝ) - Real.log (7 / 125 : ℝ) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  rw [hratio] at h
  have h1 := Real.log_lt_log (by norm_num) gaussianHazard_neg_one_gt
  have h2 := Real.log_lt_log (gaussianHazard_pos (-2)) gaussianHazard_neg_two_lt
  linarith

/-- The logarithmic separation between `-3` and `-1`. -/
theorem log_hazard_neg_one_sub_neg_three_gt :
    (4 : ℝ) < Real.log (gaussianHazard (-1)) - Real.log (gaussianHazard (-3)) := by
  have he : Real.exp 1 < (11 : ℝ) / 4 := by linarith [Real.exp_one_lt_d9]
  have he4 : Real.exp 4 < (287 : ℝ) / 5 := by
    calc
      Real.exp 4 = Real.exp 1 ^ 4 := by norm_num [← Real.exp_nat_mul]
      _ < (11 / 4 : ℝ) ^ 4 := pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
      _ < 287 / 5 := by norm_num
  have hl : (4 : ℝ) < Real.log (287 / 5) := (Real.lt_log_iff_exp_lt (by norm_num)).2 he4
  have hratio : Real.log (287 / 5 : ℝ) =
      Real.log (287 / 1000 : ℝ) - Real.log (1 / 200 : ℝ) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  rw [hratio] at hl
  have h1 := Real.log_lt_log (by norm_num) gaussianHazard_neg_one_gt
  have h2 := Real.log_lt_log (gaussianHazard_pos (-3)) gaussianHazard_neg_three_lt
  linarith

/-- The logarithmic separation between `-2` and `4`. -/
theorem log_hazard_four_sub_neg_two_gt :
    (4 : ℝ) < Real.log (gaussianHazard 4) - Real.log (gaussianHazard (-2)) := by
  have he : Real.exp 1 < (11 : ℝ) / 4 := by linarith [Real.exp_one_lt_d9]
  have he4 : Real.exp 4 < (500 : ℝ) / 7 := by
    calc
      Real.exp 4 = Real.exp 1 ^ 4 := by norm_num [← Real.exp_nat_mul]
      _ < (11 / 4 : ℝ) ^ 4 := pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
      _ < 500 / 7 := by norm_num
  have hl : (4 : ℝ) < Real.log (500 / 7) := (Real.lt_log_iff_exp_lt (by norm_num)).2 he4
  have hratio : Real.log (500 / 7 : ℝ) = Real.log 4 - Real.log (7 / 125 : ℝ) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  rw [hratio] at hl
  have h1 := Real.log_lt_log (by norm_num) gaussianHazard_four_gt
  have h2 := Real.log_lt_log (gaussianHazard_pos (-2)) gaussianHazard_neg_two_lt
  linarith

/-- The logarithmic separation between `-3` and `4`. -/
theorem log_hazard_four_sub_neg_three_gt :
    (13 : ℝ) / 2 < Real.log (gaussianHazard 4) - Real.log (gaussianHazard (-3)) := by
  have he : Real.exp 1 < (11 : ℝ) / 4 := by linarith [Real.exp_one_lt_d9]
  have he13 : Real.exp 13 < (800 : ℝ) ^ 2 := by
    calc
      Real.exp 13 = Real.exp 1 ^ 13 := by norm_num [← Real.exp_nat_mul]
      _ < (11 / 4 : ℝ) ^ 13 := pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
      _ < 800 ^ 2 := by norm_num
  have hehalf : Real.exp (13 / 2) < (800 : ℝ) := by
    have hs : Real.exp (13 / 2) ^ 2 = Real.exp 13 := by
      rw [pow_two, ← Real.exp_add]
      norm_num
    nlinarith [Real.exp_pos (13 / 2)]
  have hl : (13 : ℝ) / 2 < Real.log 800 := (Real.lt_log_iff_exp_lt (by norm_num)).2 hehalf
  have hratio : Real.log (800 : ℝ) = Real.log 4 - Real.log (1 / 200 : ℝ) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  rw [hratio] at hl
  have h1 := Real.log_lt_log (by norm_num) gaussianHazard_four_gt
  have h2 := Real.log_lt_log (gaussianHazard_pos (-3)) gaussianHazard_neg_three_lt
  linarith

end Submission.Lib.ScalarLog
