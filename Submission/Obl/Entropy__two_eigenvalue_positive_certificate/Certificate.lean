import Submission.Obl.Entropy__two_eigenvalue_positive_certificate.CoarseBounds
import Submission.Obl.Entropy__two_eigenvalue_positive_certificate.Algebra
import Submission.Obl.Entropy__two_eigenvalue_negative_certificate.Bridge

open Submission.Lib.GaussianTransport
open Submission.Obl.Entropy__two_eigenvalue_negative_certificate

namespace Submission.Obl.Entropy__two_eigenvalue_positive_certificate

lemma tail_derivative_certificate {a : ℝ} (ha : 10 ≤ a) :
    let z := deriv transportCurvature a / transportCurvature a
    (-(19/40) ≤ z ∧ z ≤ 0 ∧ transportCurvature a / (gaussianHazard a-a) ≤ 97/1000) ∧
    4/5 ≤ 1+3*transportSlope a+transportRatio a*z ∧
    1+3*transportSlope a+transportRatio a*z ≤ 177/100 := by
  dsimp only
  have hap : 0 < a := by linarith
  obtain ⟨hb, hl, hk, hp, hR, hld⟩ := coarse_bounds ha
  have hJ : 0 < scaledJ a := mul_pos hl.1 (pow_pos hap 3)
  have hRJ : 17/10 ≤ scaledR a / scaledJ a ∧ scaledR a / scaledJ a ≤ 3 := by
    constructor
    · exact (le_div_iff₀ hJ).2 hR.1
    · exact (div_le_iff₀ hJ).2 hR.2
  have hRJ0 : 0 ≤ scaledR a / scaledJ a := by linarith
  have hz : deriv transportCurvature a / transportCurvature a =
      -(scaledR a / scaledJ a / a) := by
    rw [curvature_deriv_scaledR hap, curvature_scaledJ hap]
    field_simp
    <;> ring
  have hza : 0 ≤ scaledR a / scaledJ a / a ∧ scaledR a / scaledJ a / a ≤ 3/10 := by
    constructor
    · exact div_nonneg hRJ0 hap.le
    · apply (div_le_iff₀ hap).2
      linarith
  have hkRJ : 17/20 ≤ (transportRatio a/a)*(scaledR a/scaledJ a) ∧
      (transportRatio a/a)*(scaledR a/scaledJ a) ≤ 198/125 := by
    constructor
    · have hh := mul_le_mul hk.1 hRJ.1 (by norm_num : (0:ℝ) ≤ 17/10)
        (by linarith : 0 ≤ transportRatio a/a)
      norm_num at hh
      exact hh
    · have hh := mul_le_mul hk.2 hRJ.2 hRJ0 (by norm_num : (0:ℝ) ≤ 66/125)
      norm_num at hh
      exact hh
  have hkz : transportRatio a*(deriv transportCurvature a/transportCurvature a) =
      -((transportRatio a/a)*(scaledR a/scaledJ a)) := by rw [hz]; ring
  have hchi : transportCurvature a / (gaussianHazard a-a) ≤ 97/1000 := by
    have hd := gaussianGap_pos a
    have hda : 0 < gaussianGap a*a := mul_pos hd hap
    have he : transportCurvature a / (gaussianHazard a-a) =
        (transportCurvature a*a)/(gaussianGap a*a) := by
      dsimp [gaussianGap]
      field_simp
    rw [he, div_le_iff₀ hda]
    nlinarith only [hld.1, hld.2]
  refine ⟨⟨?_, ?_, hchi⟩, ?_, ?_⟩
  · rw [hz]; linarith only [hza.2]
  · rw [hz]; linarith only [hza.1]
  · rw [hkz]; linarith only [hkRJ.2, hb.1]
  · rw [hkz]; linarith only [hkRJ.1, hb.2]

/-- The frozen certificate holds on the whole positive tail. -/
theorem raw_positive (a : ℝ) (ha : 10 ≤ a) :
    RawCertificate gaussianHazard transportRatio a := by
  have h3 : ¬ a < -3 := by linarith
  have h2 : ¬ a < -2 := by linarith
  have h1 : ¬ a < -1 := by linarith
  have hh : ¬ a < 1/2 := by linarith
  have h4 : ¬ a < 4 := by linarith
  unfold RawCertificate
  simp only [deriv_ratio, deriv_slope, deriv_auxiliary,
    if_neg h3, if_neg h2, if_neg h1, if_neg hh, if_neg h4]
  have hp : transportSlope a*(1+transportSlope a)+transportRatio a*transportCurvature a -
      (transportSlope a)^2-(40/3)*(transportCurvature a)^2 = tailP a := by
    dsimp [tailP]; ring
  have he : transportSlope a*(1+transportSlope a)+transportRatio a*transportCurvature a -
      2*(transportSlope a)^2-(80/3)*(transportCurvature a)^2+(3/4)*transportSlope a =
      tailP a-(transportSlope a)^2-(40/3)*(transportCurvature a)^2+(3/4)*transportSlope a := by
    dsimp [tailP]; ring
  simp only [hp, he]
  obtain ⟨hb, hl, hk, hp', hR, hld⟩ := coarse_bounds ha
  have halg := tail_algebra hb.1 hb.2.le hl.1.le hl.2 hp'.1 hp'.2
  have hder := tail_derivative_certificate ha
  exact ⟨by linarith, by linarith, hb.2, hl.1, halg.1, halg.2, hder.1, hder.2⟩

end Submission.Obl.Entropy__two_eigenvalue_positive_certificate
