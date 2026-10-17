import Submission.Obl.Root.GaussianCurvature
import Submission.Obl.Root.GaussianEndpoints

namespace Submission.Obl.Root.GaussianGrowth

open Submission.Lib.GaussianTransport GaussianCurvature GaussianEndpoints

noncomputable def growthFloor (a : ℝ) : ℝ :=
  if a < -3 then 0 else if a < -2 then 19 / 100 else if a < -1 then 38 / 100 else 68 / 100

/-- The complete quantitative logarithmic slope table of Lemma 2.2. -/
theorem log_M_growth_ge_floor (a : ℝ) :
    growthFloor a ≤ 2 * (1 - gaussianHazard a * gaussianGap a) / gaussianGap a ^ 2 -
      2 * transportSlope a * transportCurvature a /
        (gaussianGap a * (1 - transportSlope a ^ 2)) := by
  unfold growthFloor
  split_ifs with h3 h2 h1
  · exact (log_M_growth_pos a).le
  · exact log_M_growth_ge_nineteen (le_of_not_gt h3) gaussianHazard_neg_three_lt.le
  · exact log_M_growth_ge_thirty_eight (le_of_not_gt h2) gaussianHazard_neg_two_lt.le
  · exact log_M_growth_ge_sixty_eight (le_of_not_gt h1) gaussianHazard_neg_one_lt.le

/-- The denominator-cleared G2 expression used in Appendix A. -/
theorem cleared_growth_nonneg (a : ℝ) :
    0 ≤ 2 * (1 - gaussianHazard a * gaussianGap a) * (1 - transportSlope a ^ 2) -
      2 * transportSlope a * transportCurvature a * gaussianGap a -
      growthFloor a * gaussianGap a ^ 2 * (1 - transportSlope a ^ 2) := by
  have hb := transportSlope_pos a
  have hbhalf := transportSlope_lt_half a
  have hd := gaussianGap_pos a
  have hbs : 0 < 1 - transportSlope a ^ 2 := by nlinarith
  have h := mul_le_mul_of_nonneg_right (log_M_growth_ge_floor a)
    (mul_pos (sq_pos_of_pos hd) hbs).le
  have heq : (2 * (1 - gaussianHazard a * gaussianGap a) / gaussianGap a ^ 2 -
      2 * transportSlope a * transportCurvature a /
        (gaussianGap a * (1 - transportSlope a ^ 2))) *
          (gaussianGap a ^ 2 * (1 - transportSlope a ^ 2)) =
      2 * (1 - gaussianHazard a * gaussianGap a) * (1 - transportSlope a ^ 2) -
        2 * transportSlope a * transportCurvature a * gaussianGap a := by
    field_simp [hd.ne', hbs.ne']
  rw [heq] at h
  nlinarith

/-- The logarithmic derivative of the scalar reserve has the stated lower bound. -/
theorem reserve_derivative_ge_floor (a : ℝ) :
    growthFloor a ≤ deriv slopeReserve a / (slopeReserve a * gaussianGap a) := by
  rw [(hasDerivAt_slopeReserve a).deriv]
  have heq : gaussianGap a * slopeReserve a / (slopeReserve a * gaussianGap a) = 1 := by
    field_simp [(gaussianGap_pos a).ne', (slopeReserve_pos a).ne']
  rw [mul_div_right_comm, heq, one_mul]
  exact log_M_growth_ge_floor a

end Submission.Obl.Root.GaussianGrowth
