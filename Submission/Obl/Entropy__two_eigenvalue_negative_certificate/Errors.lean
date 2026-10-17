import Submission.Obl.Entropy__two_eigenvalue_negative_certificate.Moments
import Submission.Obl.Entropy__two_eigenvalue_negative_certificate.Density
import Submission.Obl.Entropy__two_eigenvalue_negative_certificate.Calculus

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Submission.Lib.GaussianTransport

namespace Submission.Obl.Entropy__two_eigenvalue_negative_certificate

lemma ratio_pos (a : ℝ) : 0 < transportRatio a := by
  apply div_pos _ (gaussianHazard_pos a)
  exact neg_pos.mpr (Real.log_neg (normalCDF_pos _) (normalCDF_lt_one _))

/-- The logarithmic correction to the zeroth excess moment has a fixed sign. -/
lemma ratio_moment_comparison (r : ℝ) :
    (1 - normalCDF (-r)) * moment r 0 ≤ transportRatio (-r) ∧
      transportRatio (-r) ≤ moment r 0 := by
  have hp := normalPDF_pos r
  have hc := normalCDF_pos r
  have he := normalCDF_add_neg r
  have ht := tail_eq_pdf_moment r
  have hk : transportRatio (-r) * normalPDF r =
      normalCDF r * (-Real.log (normalCDF r)) := by
    unfold transportRatio exponentialTransport gaussianHazard
    simp only [neg_neg, normalPDF_neg]
    field_simp
  have hlo := Real.log_le_sub_one_of_pos hc
  have hhi := Real.one_sub_inv_le_log_of_pos hc
  have hlo' := mul_le_mul_of_nonneg_left hlo hc.le
  have hhi' := mul_le_mul_of_nonneg_left hhi hc.le
  rw [mul_sub, mul_one, mul_inv_cancel₀ hc.ne'] at hhi'
  constructor
  · apply (mul_le_mul_iff_left₀ hp).mp
    nlinarith
  · apply (mul_le_mul_iff_left₀ hp).mp
    nlinarith

lemma tail_small_bounds {r : ℝ} (hr : 6 ≤ r) :
    normalPDF r ≤ 1 / 300 ∧ normalCDF (-r) ≤ 1 / 300 ∧
      gaussianHazard (-r) ≤ 2 * normalPDF r := by
  have hr0 : 0 < r := by linarith
  have hp := normalPDF_pos r
  have hm := moment_upper hr0 0
  norm_num at hm
  have h7 : (1 : ℝ) ≤ r ^ 7 := one_le_pow₀ (by linarith)
  have hd := density_seventh_bound hr
  have hpdf : normalPDF r ≤ 1 / 300 := by
    nlinarith [mul_le_mul_of_nonneg_right h7 hp.le]
  have hmr : moment r 0 * r ≤ 1 := (le_div_iff₀ hr0).mp (by simpa only [one_div] using hm)
  have hm1 : moment r 0 ≤ 1 := by
    nlinarith [moment_nonneg r 0]
  have hc : normalCDF (-r) ≤ 1 / 300 := by
    rw [tail_eq_pdf_moment]
    nlinarith
  refine ⟨hpdf, hc, ?_⟩
  unfold gaussianHazard
  rw [normalPDF_neg, neg_neg, div_le_iff₀ (normalCDF_pos r)]
  have hh := normalCDF_add_neg r
  nlinarith

/-- Error bounds with denominators cleared; these are stable under the recurrences. -/
lemma basic_error_bounds {r : ℝ} (hr : 6 ≤ r) :
    0 ≤ moment r 0 - transportRatio (-r) ∧
    (moment r 0 - transportRatio (-r)) * r ^ 2 ≤ normalPDF r ∧
    transportRatio (-r) * r ≤ 1 ∧
    |transportSlope (-r) - moment r 1| * r ≤ 3 * normalPDF r ∧
    |transportCurvature (-r) - moment r 2| ≤ 6 * normalPDF r ∧
    |deriv transportCurvature (-r) - moment r 3| ≤ 9 * r * normalPDF r := by
  have hr0 : 0 < r := by linarith
  have hp := normalPDF_pos r
  have hk0 := ratio_pos (-r)
  have hq0 := gaussianHazard_pos (-r)
  obtain ⟨hpdf, hcsmall, hq⟩ := tail_small_bounds hr
  obtain ⟨hkl, hku⟩ := ratio_moment_comparison r
  have hm := moment_upper hr0 0
  norm_num at hm
  have hm0 := moment_nonneg r 0
  have hmr : moment r 0 * r ≤ 1 := (le_div_iff₀ hr0).mp (by simpa only [one_div] using hm)
  have hkr : transportRatio (-r) * r ≤ 1 := by nlinarith
  have hδ0 : 0 ≤ moment r 0 - transportRatio (-r) := sub_nonneg.mpr hku
  have hδ : (moment r 0 - transportRatio (-r)) * r ^ 2 ≤ normalPDF r := by
    rw [tail_eq_pdf_moment] at hkl
    have hmr0 : 0 ≤ moment r 0 * r := mul_nonneg hm0 hr0.le
    have hsq : (moment r 0 * r) ^ 2 ≤ 1 := by nlinarith
    have h1 := mul_le_mul_of_nonneg_right hkl (sq_nonneg r)
    have h2 := mul_le_mul_of_nonneg_left hsq hp.le
    nlinarith
  have hb : transportSlope (-r) - moment r 1 =
      r * (moment r 0 - transportRatio (-r)) - transportRatio (-r) * gaussianHazard (-r) := by
    rw [moment_one hr0]
    unfold transportSlope gaussianGap
    ring
  have hqk : transportRatio (-r) * gaussianHazard (-r) * r ≤ 2 * normalPDF r := by
    have h1 := mul_le_mul_of_nonneg_left hq (mul_nonneg hk0.le hr0.le)
    have h2 := mul_le_mul_of_nonneg_right hkr (by positivity : 0 ≤ 2 * normalPDF r)
    nlinarith
  have hbabs : |transportSlope (-r) - moment r 1| * r ≤ 3 * normalPDF r := by
    rw [show |transportSlope (-r) - moment r 1| * r =
      |(transportSlope (-r) - moment r 1) * r| by rw [abs_mul, abs_of_pos hr0], abs_le, hb]
    constructor
    · nlinarith [mul_nonneg hδ0 (sq_nonneg r)]
    · nlinarith [mul_nonneg hk0.le hq0.le]
  have hl : transportCurvature (-r) - moment r 2 =
      -(moment r 0 - transportRatio (-r)) - gaussianHazard (-r) -
        r * (transportSlope (-r) - moment r 1) := by
    have hm2 := moment_recurrence hr0 0
    norm_num at hm2
    rw [hm2]
    unfold transportCurvature
    ring
  have hδsmall : moment r 0 - transportRatio (-r) ≤ normalPDF r := by
    have hr2 : 1 ≤ r ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hr2 hδ0]
  have hlabs : |transportCurvature (-r) - moment r 2| ≤ 6 * normalPDF r := by
    have hbabs' : |r * (transportSlope (-r) - moment r 1)| ≤ 3 * normalPDF r := by
      simpa only [abs_mul, abs_of_pos hr0, mul_comm] using hbabs
    have hbpm := abs_le.mp hbabs'
    rw [hl, abs_le]
    constructor <;> nlinarith
  have hlp : deriv transportCurvature (-r) - moment r 3 =
      2 * (transportSlope (-r) - moment r 1) -
        gaussianHazard (-r) * (gaussianHazard (-r) + r) -
        r * (transportCurvature (-r) - moment r 2) := by
    have hm3 := moment_recurrence hr0 1
    norm_num at hm3
    rw [deriv_curvature, hm3]
    unfold gaussianGap
    ring
  have hq1 : gaussianHazard (-r) ≤ 1 := by linarith
  have hbsmall : 2 * |transportSlope (-r) - moment r 1| ≤ normalPDF r := by
    nlinarith [abs_nonneg (transportSlope (-r) - moment r 1)]
  have hqprod : gaussianHazard (-r) * (gaussianHazard (-r) + r) ≤
      2 * normalPDF r + 2 * r * normalPDF r := by
    nlinarith only [hq, mul_le_mul_of_nonneg_right hq hr0.le,
      mul_nonneg hq0.le (sub_nonneg.mpr hq1)]
  have hlpm := abs_le.mp hlabs
  have hbpm := abs_le.mp (show |transportSlope (-r) - moment r 1| ≤ normalPDF r / 2 by linarith)
  have hlpabs : |deriv transportCurvature (-r) - moment r 3| ≤ 9 * r * normalPDF r := by
    rw [hlp, abs_le]
    have hp6 : 6 * normalPDF r ≤ r * normalPDF r := by nlinarith
    have h1 := mul_le_mul_of_nonneg_left hlpm.1 hr0.le
    have h2 := mul_le_mul_of_nonneg_left hlpm.2 hr0.le
    constructor <;> nlinarith only [hbpm.1, hbpm.2, hqprod, h1, h2, hp6,
      mul_nonneg hq0.le (by positivity : 0 ≤ gaussianHazard (-r) + r)]
  exact ⟨hδ0, hδ, hkr, hbabs, hlabs, hlpabs⟩

end Submission.Obl.Entropy__two_eigenvalue_negative_certificate
