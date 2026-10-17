import Submission.Obl.Entropy__hazard_secant_surplus.Monotonicity

open Set

namespace Submission.Obl.Entropy__hazard_secant_surplus

open Submission.Lib.GaussianTransport

/-- The final polynomial in group G2 of the supplied certificate. -/
def GrowthCertificate : Prop := ∀ a : ℝ,
  growthStep a * gaussianGap a ^ 2 * (1 - transportSlope a ^ 2) ≤
    2 * (1 - gaussianHazard a * gaussianGap a) * (1 - transportSlope a ^ 2) -
      2 * transportSlope a * transportCurvature a * gaussianGap a

lemma hasDerivAt_scalarM (a : ℝ) :
    HasDerivAt scalarM
      ((2 * (1 - gaussianHazard a * gaussianGap a) * (1 - transportSlope a ^ 2) -
        2 * transportSlope a * transportCurvature a * gaussianGap a) / gaussianGap a ^ 3) a := by
  convert! (((hasDerivAt_transportSlope a).pow 2).const_sub 1).div
    ((hasDerivAt_gaussianGap a).pow 2) (pow_ne_zero 2 (ne_of_gt (gaussianGap_pos a))) using 1
  simp only [Pi.pow_apply]
  field_simp [ne_of_gt (gaussianGap_pos a)]
  ring

lemma growth_inequality (h : GrowthCertificate) (a : ℝ) :
    growthStep a * scalarM a * gaussianGap a ≤ deriv scalarM a := by
  rw [(hasDerivAt_scalarM a).deriv]
  apply (le_div_iff₀ (pow_pos (gaussianGap_pos a) 3)).2
  calc
    _ = growthStep a * gaussianGap a ^ 2 * (1 - transportSlope a ^ 2) := by
      unfold scalarM
      field_simp [ne_of_gt (gaussianGap_pos a)]
    _ ≤ _ := h a

lemma monotone_scalarM (h : GrowthCertificate) : Monotone scalarM := by
  apply monotone_of_deriv_nonneg (fun a => (hasDerivAt_scalarM a).differentiableAt)
  intro a
  exact (mul_nonneg (mul_nonneg (growthStep_nonneg a) (scalarM_pos a).le)
    (gaussianGap_pos a).le).trans (growth_inequality h a)

lemma monotone_transportRatio : Monotone transportRatio :=
  (strictMono_of_hasDerivAt_pos hasDerivAt_transportRatio transportSlope_pos).monotone

lemma monotone_transportSlope (hl : ∀ a, 0 ≤ transportCurvature a) : Monotone transportSlope := by
  apply monotone_of_deriv_nonneg (fun a => (hasDerivAt_transportSlope a).differentiableAt)
  intro a
  simpa only [(hasDerivAt_transportSlope a).deriv] using hl a

lemma monotone_other_factor (hl : ∀ a, 0 ≤ transportCurvature a) :
    Monotone (fun a => (1 + transportSlope a) / gaussianGap a) := by
  intro a b hab
  apply div_le_div₀
  · have hb := transportSlope_pos b
    positivity
  · exact add_le_add_right (monotone_transportSlope hl hab) 1
  · exact gaussianGap_pos b
  · exact antitone_gaussianGap hab

end Submission.Obl.Entropy__hazard_secant_surplus
