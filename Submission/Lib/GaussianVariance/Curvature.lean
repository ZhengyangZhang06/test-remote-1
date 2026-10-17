/- Analytic normalized-variance and curvature bounds for the Gaussian hazard.
Developed in this tree for o029 by x0076. -/

import Submission.Lib.GaussianVariance.VarianceFloor

open Set Filter
open scoped Topology

namespace Submission.Lib.GaussianVariance

open Submission.Lib.GaussianTransport

noncomputable def normalizedVariance (a : ℝ) : ℝ :=
  (1 - gaussianHazard a * gaussianGap a) / gaussianGap a ^ 2

lemma normalizedVariance_pos (a : ℝ) : 0 < normalizedVariance a :=
  div_pos (one_sub_hazard_mul_gap_pos a) (sq_pos_of_pos (gaussianGap_pos a))

lemma varianceDefect_normalizedVariance (a : ℝ) : varianceDefect (normalizedVariance a) a = 0 := by
  unfold varianceDefect normalizedVariance
  field_simp [ne_of_gt (gaussianGap_pos a)]
  ring

lemma monotone_normalizedVariance : Monotone normalizedVariance := by
  intro a s has
  apply (le_div_iff₀ (sq_pos_of_pos (gaussianGap_pos s))).mpr
  have h := varianceDefect_nonneg_of_le (normalizedVariance_pos a).le
    (le_of_eq (varianceDefect_normalizedVariance a).symm) has
  unfold varianceDefect at h
  linarith

lemma tendsto_gap_atBot : Tendsto gaussianGap atBot atTop := by
  apply tendsto_atTop_mono (f := fun x : ℝ => -x) _ tendsto_neg_atBot_atTop
  intro x
  unfold gaussianGap
  linarith [gaussianHazard_pos x]

lemma tendsto_transport_atBot : Tendsto exponentialTransport atBot (𝓝 0) := by
  have h : Tendsto (fun x => normalCDF (-x)) atBot (𝓝 1) :=
    (ProbabilityTheory.tendsto_cdf_atTop (ProbabilityTheory.gaussianReal 0 1)).comp
      tendsto_neg_atBot_atTop
  change Tendsto (fun x => -Real.log (normalCDF (-x))) atBot (𝓝 0)
  simpa only [Real.log_one, neg_zero] using (h.log one_ne_zero).neg

lemma comparison_nonneg (a : ℝ) :
    gaussianHazard a / gaussianGap a / (1 + normalizedVariance a) ≤ exponentialTransport a := by
  let F : ℝ → ℝ := fun x => exponentialTransport x -
    gaussianHazard x / gaussianGap x / (1 + normalizedVariance a)
  have ha : 0 < 1 + normalizedVariance a := by linarith [normalizedVariance_pos a]
  have hd (x : ℝ) : HasDerivAt F
      (gaussianHazard x * (1 - (1 + normalizedVariance x) / (1 + normalizedVariance a))) x := by
    convert! (hasDerivAt_exponentialTransport x).sub
      (((hasDerivAt_gaussianHazard x).div (hasDerivAt_gaussianGap x)
        (ne_of_gt (gaussianGap_pos x))).div_const (1 + normalizedVariance a)) using 1
    change _ = gaussianHazard x -
      ((gaussianHazard x * gaussianGap x * gaussianGap x -
        gaussianHazard x * (gaussianHazard x * gaussianGap x - 1)) / gaussianGap x ^ 2) /
          (1 + normalizedVariance a)
    unfold normalizedVariance
    field_simp [ne_of_gt (gaussianGap_pos x), ne_of_gt ha]
    ring
  have hm : MonotoneOn F (Iic a) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Iic _)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd x).hasDerivWithinAt
    · intro x hx
      apply mul_nonneg (gaussianHazard_pos x).le
      apply sub_nonneg.mpr
      apply (div_le_one ha).mpr
      have hx' : x ≤ a := (show x < a from by simpa only [interior_Iic, mem_Iio] using hx).le
      exact add_le_add_right (monotone_normalizedVariance hx') 1
  have ht : Tendsto F atBot (𝓝 0) := by
    simpa only [F, zero_div, sub_zero] using tendsto_transport_atBot.sub
      ((tendsto_gaussianHazard_atBot.div_atTop tendsto_gap_atBot).div_const (1 + normalizedVariance a))
  have hn : 0 ≤ F a := le_of_tendsto ht
    (by filter_upwards [eventually_le_atBot a] with x hx; exact hm hx self_mem_Iic hx)
  exact sub_nonneg.mp hn

lemma transportCurvature_nonneg (a : ℝ) : 0 ≤ transportCurvature a := by
  have ha : 0 < 1 + normalizedVariance a := by linarith [normalizedVariance_pos a]
  have h1 := (div_le_iff₀ ha).mp (comparison_nonneg a)
  have h2 := (div_le_iff₀ (gaussianGap_pos a)).mp h1
  rw [← gaussianHazard_mul_transportRatio a] at h2
  have h3 : 1 ≤ transportRatio a * gaussianGap a * (1 + normalizedVariance a) := by
    apply (mul_le_mul_iff_right₀ (gaussianHazard_pos a)).mp
    nlinarith [h2]
  have heq : transportRatio a * gaussianGap a * (1 + normalizedVariance a) - 1 =
      transportCurvature a / gaussianGap a := by
    unfold normalizedVariance transportCurvature transportSlope
    field_simp [ne_of_gt (gaussianGap_pos a)]
    unfold gaussianGap
    ring
  have h4 : 0 ≤ transportCurvature a / gaussianGap a := by rw [← heq]; linarith
  simpa only [div_mul_cancel₀ _ (ne_of_gt (gaussianGap_pos a))] using
    mul_nonneg h4 (gaussianGap_pos a).le

end Submission.Lib.GaussianVariance
