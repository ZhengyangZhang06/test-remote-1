/-
Adapted from: here:o001

Original proofs by session x0021, building on the Gaussian scalar
calculus developed by x0004 in this workspace.
-/

import Submission.Lib.GaussianTransport.GaussianConvexity

/-! The slope bounds in Lemma 2.2, obtained from Lemma 2.1's strict variance comparison. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff

namespace Submission.Lib.GaussianTransport

private theorem tendsto_gap_atBot : Tendsto gaussianGap atBot atTop := by
  apply tendsto_atTop_mono (f := fun a : ℝ => -a) _ tendsto_neg_atBot_atTop
  intro a
  have h := gaussianHazard_pos a
  dsimp only [gaussianGap]
  linarith

private theorem tendsto_transport_atBot : Tendsto exponentialTransport atBot (𝓝 0) := by
  have hc : Tendsto (fun x => normalCDF (-x)) atBot (𝓝 1) :=
    (tendsto_cdf_atTop (gaussianReal 0 1)).comp tendsto_neg_atBot_atTop
  change Tendsto (fun x => -Real.log (normalCDF (-x))) atBot (𝓝 0)
  simpa only [Real.log_one, neg_zero] using (hc.log one_ne_zero).neg

private theorem tendsto_comparison_atBot (c : ℝ) :
    Tendsto (fun x => c * (gaussianHazard x / gaussianGap x) - exponentialTransport x)
      atBot (𝓝 0) := by
  have h := (tendsto_gaussianHazard_atBot.div_atTop tendsto_gap_atBot).const_mul c
  simpa using h.sub tendsto_transport_atBot

private theorem hasDerivAt_comparison (c a : ℝ) :
    HasDerivAt (fun x => c * (gaussianHazard x / gaussianGap x) - exponentialTransport x)
      (gaussianHazard a * (c * (1 +
        (1 - gaussianHazard a * gaussianGap a) / gaussianGap a ^ 2) - 1)) a := by
  convert! (((hasDerivAt_gaussianHazard a).div (hasDerivAt_gaussianGap a)
    (ne_of_gt (gaussianGap_pos a))).const_mul c).sub
      (hasDerivAt_exponentialTransport a) using 1
  change _ = c * ((gaussianHazard a * gaussianGap a * gaussianGap a -
    gaussianHazard a * (gaussianHazard a * gaussianGap a - 1)) / gaussianGap a ^ 2) -
      gaussianHazard a
  field_simp [ne_of_gt (gaussianGap_pos a)]
  ring

/-- The first strict scalar slope bound in Lemma 2.2. -/
theorem transportSlope_pos (a : ℝ) : 0 < transportSlope a := by
  have hm : StrictMono (fun x => gaussianHazard x / gaussianGap x - exponentialTransport x) := by
    apply strictMono_of_hasDerivAt_pos
      (fun x => by simpa using hasDerivAt_comparison 1 x)
    intro x
    have h := div_pos (one_sub_hazard_mul_gap_pos x) (sq_pos_of_pos (gaussianGap_pos x))
    have hq := gaussianHazard_pos x
    nlinarith
  have ht : Tendsto (fun x => gaussianHazard x / gaussianGap x - exponentialTransport x)
      atBot (𝓝 0) := by simpa using tendsto_comparison_atBot 1
  have hn := hm.monotone.le_of_tendsto ht (a - 1)
  have hlt := hm (show a - 1 < a by linarith)
  have hb : exponentialTransport a < gaussianHazard a / gaussianGap a := by linarith
  have hb' := (lt_div_iff₀ (gaussianGap_pos a)).mp hb
  unfold transportSlope transportRatio
  have hq := gaussianHazard_pos a
  have htq : exponentialTransport a / gaussianHazard a * gaussianGap a < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one hq]
    exact hb'
  linarith

/-- The second strict scalar slope bound in Lemma 2.2. -/
theorem transportSlope_lt_half (a : ℝ) : transportSlope a < 1 / 2 := by
  have hm : StrictAnti (fun x => (1 / 2 : ℝ) * (gaussianHazard x / gaussianGap x) -
      exponentialTransport x) := by
    apply strictAnti_of_hasDerivAt_neg (hasDerivAt_comparison (1 / 2))
    intro x
    have h := (div_lt_one (sq_pos_of_pos (gaussianGap_pos x))).2
      (one_sub_hazard_mul_gap_lt_gap_sq x)
    apply mul_neg_of_pos_of_neg (gaussianHazard_pos x)
    linarith
  have hn := hm.antitone.ge_of_tendsto (tendsto_comparison_atBot (1 / 2)) (a - 1)
  have hlt := hm (show a - 1 < a by linarith)
  have hb : gaussianHazard a / gaussianGap a < 2 * exponentialTransport a := by linarith
  have hb' := (div_lt_iff₀ (gaussianGap_pos a)).mp hb
  unfold transportSlope transportRatio
  have hq := gaussianHazard_pos a
  have htq : (1 / 2 : ℝ) < exponentialTransport a / gaussianHazard a * gaussianGap a := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ hq]
    linarith
  linarith

end Submission.Lib.GaussianTransport
