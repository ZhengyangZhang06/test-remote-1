import Submission.Obl.Entropy__hazard_secant_surplus.Growth
import Submission.Obl.Entropy__hazard_secant_surplus.Curvature
import Submission.Obl.Entropy__hazard_secant_surplus.Endpoints

namespace Submission.Obl.Entropy__hazard_secant_surplus

open Submission.Lib.GaussianTransport

lemma normalizedVariance_neg_three : (1 / 10 : ℝ) ≤ normalizedVariance (-3) := by
  unfold normalizedVariance
  apply (le_div_iff₀ (sq_pos_of_pos (gaussianGap_pos (-3)))).mpr
  unfold gaussianGap
  have h := gaussianHazard_neg_three_le
  have hp := gaussianHazard_pos (-3)
  have hs := (sq_le_sq₀ hp.le (by norm_num : (0 : ℝ) ≤ 1 / 100)).mpr h
  nlinarith

lemma normalizedVariance_neg_two : (1 / 5 : ℝ) ≤ normalizedVariance (-2) := by
  unfold normalizedVariance
  apply (le_div_iff₀ (sq_pos_of_pos (gaussianGap_pos (-2)))).mpr
  unfold gaussianGap
  have h := gaussianHazard_neg_two_le
  have hp := gaussianHazard_pos (-2)
  have hs := (sq_le_sq₀ hp.le (by norm_num : (0 : ℝ) ≤ 1 / 15)).mpr h
  nlinarith

lemma normalizedVariance_neg_one : (11 / 30 : ℝ) ≤ normalizedVariance (-1) := by
  unfold normalizedVariance
  apply (le_div_iff₀ (sq_pos_of_pos (gaussianGap_pos (-1)))).mpr
  unfold gaussianGap
  have h := gaussianHazard_neg_one_le
  have hp := gaussianHazard_pos (-1)
  have hs := (sq_le_sq₀ hp.le (by norm_num : (0 : ℝ) ≤ 59 / 200)).mpr h
  nlinarith

lemma scalarM_numerator_identity (a : ℝ) :
    2 * (1 - gaussianHazard a * gaussianGap a) * (1 - transportSlope a ^ 2) -
      2 * transportSlope a * transportCurvature a * gaussianGap a =
    2 * ((1 - gaussianHazard a * gaussianGap a) * (1 - transportSlope a) +
      gaussianGap a ^ 2 * transportSlope a ^ 2) := by
  unfold transportCurvature transportSlope gaussianGap
  ring

lemma growth_from_variance {a r m : ℝ} (hm : 0 ≤ m)
    (hR : r ≤ normalizedVariance a) (hr : r ^ 2 ≤ (2 + m) * (2 * r - m)) :
    m * gaussianGap a ^ 2 * (1 - transportSlope a ^ 2) ≤
      2 * (1 - gaussianHazard a * gaussianGap a) * (1 - transportSlope a ^ 2) -
        2 * transportSlope a * transportCurvature a * gaussianGap a := by
  rw [scalarM_numerator_identity]
  have hb : 0 ≤ 1 - transportSlope a := by linarith [transportSlope_lt_half a]
  have hD := sq_pos_of_pos (gaussianGap_pos a)
  have hR' : r * gaussianGap a ^ 2 ≤ 1 - gaussianHazard a * gaussianGap a :=
    (le_div_iff₀ hD).mp hR
  have hmul := mul_le_mul_of_nonneg_right hR' hb
  have hquad : m * (1 - transportSlope a ^ 2) ≤
      2 * (r * (1 - transportSlope a) + transportSlope a ^ 2) := by
    have hs := sq_nonneg ((2 + m) * transportSlope a - r)
    have hn : 0 ≤ (2 + m) *
        ((2 + m) * transportSlope a ^ 2 - 2 * r * transportSlope a + 2 * r - m) := by
      nlinarith
    have hmpos : 0 < 2 + m := by linarith
    have ht : 0 ≤ (2 + m) * transportSlope a ^ 2 - 2 * r * transportSlope a + 2 * r - m :=
      nonneg_of_mul_nonneg_right hn hmpos
    nlinarith
  have hquadD := mul_le_mul_of_nonneg_right hquad hD.le
  nlinarith

lemma growth_certificate : GrowthCertificate := by
  intro a
  unfold growthStep
  split_ifs with h3 h2 h1
  · rw [zero_mul, zero_mul, scalarM_numerator_identity]
    exact mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg (one_sub_hazard_mul_gap_pos a).le
        (by linarith [transportSlope_lt_half a])) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  · exact growth_from_variance (r := 1 / 10) (by norm_num)
      (normalizedVariance_neg_three.trans (monotone_normalizedVariance (by linarith))) (by norm_num)
  · exact growth_from_variance (r := 1 / 5) (by norm_num)
      (normalizedVariance_neg_two.trans (monotone_normalizedVariance (by linarith))) (by norm_num)
  · exact growth_from_variance (r := 11 / 30) (by norm_num)
      (normalizedVariance_neg_one.trans (monotone_normalizedVariance (by linarith))) (by norm_num)

end Submission.Obl.Entropy__hazard_secant_surplus
