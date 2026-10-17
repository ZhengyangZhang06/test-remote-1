import Submission.Obl.Entropy__two_eigenvalue_negative_certificate.Errors
import Submission.Obl.Entropy__two_eigenvalue_negative_certificate.Rational

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Submission.Lib.GaussianTransport

namespace Submission.Obl.Entropy__two_eigenvalue_negative_certificate

lemma scaled_error_bounds {r : ℝ} (hr : 6 ≤ r) :
    |transportSlope (-r) - moment r 1| * r ^ 4 ≤ 1 / 100 ∧
    |transportCurvature (-r) - moment r 2| * r ^ 5 ≤ 1 / 50 ∧
    |deriv transportCurvature (-r) - moment r 3| * r ^ 6 ≤ 3 / 50 := by
  have hr0 : 0 < r := by linarith
  have hp := normalPDF_pos r
  obtain ⟨_, _, _, hb, hl, ht⟩ := basic_error_bounds hr
  have hd := density_seventh_bound hr
  have h4 : (1 : ℝ) ≤ r ^ 4 := one_le_pow₀ (by linarith)
  have h2 : (36 : ℝ) ≤ r ^ 2 := by nlinarith
  have h3 := mul_le_mul_of_nonneg_right h4 (by positivity : 0 ≤ r ^ 3 * normalPDF r)
  have h5 := mul_le_mul_of_nonneg_right h2 (by positivity : 0 ≤ r ^ 5 * normalPDF r)
  have hbp := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ r ^ 3)
  have hlp := mul_le_mul_of_nonneg_right hl (by positivity : 0 ≤ r ^ 5)
  have htp := mul_le_mul_of_nonneg_right ht (by positivity : 0 ≤ r ^ 6)
  constructor
  · nlinarith only [hd, h3, hbp]
  constructor
  · nlinarith only [hd, h5, hlp]
  · nlinarith only [hd, htp]

/-- Inverse powers, with the small Gaussian correction included. -/
lemma derivative_enclosures {r : ℝ} (hr : 6 ≤ r) :
    r ^ 2 - 301 / 100 ≤ transportSlope (-r) * r ^ 4 ∧
    transportSlope (-r) * r ^ 4 ≤ r ^ 2 + 1 / 100 ∧
    2 * r ^ 2 - 601 / 50 ≤ transportCurvature (-r) * r ^ 5 ∧
    transportCurvature (-r) * r ^ 5 ≤ 2 * r ^ 2 + 1 / 50 ∧
    6 * r ^ 2 - 3003 / 50 ≤ deriv transportCurvature (-r) * r ^ 6 ∧
    deriv transportCurvature (-r) * r ^ 6 ≤ 6 * r ^ 2 + 3 / 50 := by
  have hr0 : 0 < r := by linarith
  have hrne := hr0.ne'
  obtain ⟨hb, hl, ht⟩ := scaled_error_bounds hr
  have hb' : |(transportSlope (-r) - moment r 1) * r ^ 4| ≤ 1 / 100 := by
    simpa only [abs_mul, abs_of_pos (pow_pos hr0 4)] using hb
  have hl' : |(transportCurvature (-r) - moment r 2) * r ^ 5| ≤ 1 / 50 := by
    simpa only [abs_mul, abs_of_pos (pow_pos hr0 5)] using hl
  have ht' : |(deriv transportCurvature (-r) - moment r 3) * r ^ 6| ≤ 3 / 50 := by
    simpa only [abs_mul, abs_of_pos (pow_pos hr0 6)] using ht
  obtain ⟨hbm, hbp⟩ := abs_le.mp hb'
  obtain ⟨hlm, hlp⟩ := abs_le.mp hl'
  obtain ⟨htm, htp⟩ := abs_le.mp ht'
  have h1l := moment_lower hr0 1
  have h1u := moment_upper hr0 1
  have h2l := moment_lower hr0 2
  have h2u := moment_upper hr0 2
  have h3l := moment_lower hr0 3
  have h3u := moment_upper hr0 3
  norm_num [Nat.factorial] at h1l h1u h2l h2u h3l h3u
  have hi1l : r ^ 2 - 3 ≤ moment r 1 * r ^ 4 := by
    have h := mul_le_mul_of_nonneg_right h1l (by positivity : 0 ≤ r ^ 4)
    field_simp at h
    nlinarith only [h]
  have hi1u : moment r 1 * r ^ 4 ≤ r ^ 2 := by
    have h := mul_le_mul_of_nonneg_right h1u (by positivity : 0 ≤ r ^ 4)
    field_simp at h
    nlinarith only [mul_le_mul_of_nonneg_right h (sq_nonneg r)]
  have hi2l : 2 * r ^ 2 - 12 ≤ moment r 2 * r ^ 5 := by
    have h := mul_le_mul_of_nonneg_right h2l (by positivity : 0 ≤ r ^ 5)
    field_simp at h
    nlinarith only [h]
  have hi2u : moment r 2 * r ^ 5 ≤ 2 * r ^ 2 := by
    have h := mul_le_mul_of_nonneg_right h2u (by positivity : 0 ≤ r ^ 5)
    field_simp at h
    nlinarith only [mul_le_mul_of_nonneg_right h (sq_nonneg r)]
  have hi3l : 6 * r ^ 2 - 60 ≤ moment r 3 * r ^ 6 := by
    have h := mul_le_mul_of_nonneg_right h3l (by positivity : 0 ≤ r ^ 6)
    field_simp at h
    nlinarith only [h]
  have hi3u : moment r 3 * r ^ 6 ≤ 6 * r ^ 2 := by
    have h := mul_le_mul_of_nonneg_right h3u (by positivity : 0 ≤ r ^ 6)
    field_simp at h
    nlinarith only [mul_le_mul_of_nonneg_right h (sq_nonneg r)]
  exact ⟨by nlinarith only [hbm, hi1l], by nlinarith only [hbp, hi1u],
    by nlinarith only [hlm, hi2l], by nlinarith only [hlp, hi2u],
    by nlinarith only [htm, hi3l], by nlinarith only [htp, hi3u]⟩

lemma normalized_enclosures {r : ℝ} (hr : 6 ≤ r) :
    TailData r⁻¹ (transportRatio (-r)) (transportSlope (-r))
      (transportCurvature (-r)) (deriv transportCurvature (-r)) := by
  have hr0 : 0 < r := by linarith
  have hrne := hr0.ne'
  have hk := (basic_error_bounds hr).2.2.1
  obtain ⟨hbl, hbu, hll, hlu, htl, htu⟩ := derivative_enclosures hr
  refine ⟨inv_pos.mpr hr0, ?_, ratio_pos (-r), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [inv_eq_one_div, div_le_div_iff₀ hr0 (by norm_num)]
    linarith
  · rw [inv_eq_one_div, le_div_iff₀ hr0]
    exact hk
  · have h := mul_le_mul_of_nonneg_right hbl (by positivity : 0 ≤ r⁻¹ ^ 4)
    convert! h using 1 <;> field_simp <;> ring
  · have h := mul_le_mul_of_nonneg_right hbu (by positivity : 0 ≤ r⁻¹ ^ 4)
    convert! h using 1 <;> field_simp <;> ring
  · have h := mul_le_mul_of_nonneg_right hll (by positivity : 0 ≤ r⁻¹ ^ 5)
    convert! h using 1 <;> field_simp <;> ring
  · have h := mul_le_mul_of_nonneg_right hlu (by positivity : 0 ≤ r⁻¹ ^ 5)
    convert! h using 1 <;> field_simp <;> ring
  · have h := mul_le_mul_of_nonneg_right htl (by positivity : 0 ≤ r⁻¹ ^ 6)
    convert! h using 1 <;> field_simp <;> ring
  · have h := mul_le_mul_of_nonneg_right htu (by positivity : 0 ≤ r⁻¹ ^ 6)
    convert! h using 1 <;> field_simp <;> ring

end Submission.Obl.Entropy__two_eigenvalue_negative_certificate
