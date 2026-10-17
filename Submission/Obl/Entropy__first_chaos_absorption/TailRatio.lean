import Submission.Obl.Entropy__first_chaos_absorption.Mills

open MeasureTheory ProbabilityTheory

namespace Submission.Obl.Entropy__first_chaos_absorption

set_option backward.isDefEq.respectTransparency false

open Submission.Lib.GaussianTransport

/-- The Mills ratio differs from the transport ratio only by a small positive
logarithmic correction. This estimate holds without a tail restriction. -/
lemma transportRatio_mills_bounds (r : ℝ) :
    (1-normalCDF (-r)) * (normalCDF (-r)/normalPDF r) ≤ transportRatio (-r) ∧
    transportRatio (-r) ≤ normalCDF (-r)/normalPDF r := by
  have hP := normalCDF_pos r
  have hsym := normalCDF_add_neg r
  have hform : transportRatio (-r) = normalCDF r * (-Real.log (normalCDF r)) / normalPDF r := by
    simp only [transportRatio, exponentialTransport, gaussianHazard, neg_neg, normalPDF_neg]
    field_simp
  rw [hform]
  constructor
  · rw [← mul_div_assoc]
    apply (div_le_div_iff_of_pos_right (normalPDF_pos r)).mpr
    have hlog := Real.log_le_sub_one_of_pos hP
    have hmul := mul_le_mul_of_nonneg_left (show normalCDF (-r) ≤ -Real.log (normalCDF r) by linarith) hP.le
    rw [show 1-normalCDF (-r) = normalCDF r by linarith]
    exact hmul
  · apply (div_le_div_iff_of_pos_right (normalPDF_pos r)).mpr
    have hlog := Real.one_sub_inv_le_log_of_pos hP
    have hmul := mul_le_mul_of_nonneg_left hlog hP.le
    have hi : normalCDF r * (normalCDF r)⁻¹ = 1 := mul_inv_cancel₀ hP.ne'
    nlinarith only [hmul, hsym, hi]

lemma mills_upper_zero {r : ℝ} (hr : 0 < r) :
    normalCDF (-r)/normalPDF r ≤ r⁻¹ := by
  have h := normalPDF_sub_mul_normalCDF_pos r
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hr).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (normalPDF_pos r)).mpr
  linarith

/-- A simple Gaussian error bound for the ratio in the negative tail. -/
lemma transportRatio_tail_error {r : ℝ} (hr : 0 < r) :
    normalCDF (-r)/normalPDF r - normalPDF r*(r⁻¹)^2 ≤ transportRatio (-r) ∧
    transportRatio (-r) ≤ normalCDF (-r)/normalPDF r := by
  obtain ⟨hl, hu⟩ := transportRatio_mills_bounds r
  refine ⟨?_, hu⟩
  have hI := mills_upper_zero hr
  have hP : normalCDF (-r) ≤ normalPDF r*r⁻¹ := by
    simpa only [mul_comm] using (div_le_iff₀ (normalPDF_pos r)).mp hI
  have hprod : normalCDF (-r)*(normalCDF (-r)/normalPDF r) ≤ normalPDF r*(r⁻¹)^2 := by
    calc
      _ ≤ (normalPDF r*r⁻¹)*r⁻¹ :=
        mul_le_mul hP hI (div_nonneg (normalCDF_pos _).le (normalPDF_pos _).le)
          (mul_nonneg (normalPDF_pos _).le (inv_nonneg.mpr hr.le))
      _ = _ := by ring
  nlinarith only [hl, hprod]

end Submission.Obl.Entropy__first_chaos_absorption
