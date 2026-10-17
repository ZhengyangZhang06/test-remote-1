import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Mills

namespace Submission.Obl.Entropy__two_eigenvalue_compact_certificate
open Submission.Lib.GaussianTransport

set_option maxRecDepth 10000 in
 theorem hazard_anchor : |gaussianHazard 10 - 10098093234/10^9| < 4/10^10 := by
  have hlo := mills_11_lower (x := 10) (by norm_num)
  have hhi := mills_12_upper (x := 10) (by norm_num)
  have hl : 1/(100980932343/10^10 : ℝ) ≤ normalCDF (-10) / normalPDF 10 := by
    apply le_trans _ hlo
    norm_num [millsPoly, millsCoeff, peval, List.range_succ]
  have hu : normalCDF (-10) / normalPDF 10 ≤ 1/(100980932337/10^10 : ℝ) := by
    apply le_trans hhi
    norm_num [millsPoly, millsCoeff, peval, List.range_succ]
  have hp := normalPDF_pos 10
  have hc := normalCDF_pos (-10)
  have hl' := (le_div_iff₀ hp).mp hl
  have hu' := (div_le_iff₀ hp).mp hu
  have hqU : gaussianHazard 10 ≤ 100980932343/10^10 := by
    change normalPDF 10 / normalCDF (-10) ≤ _
    apply (div_le_iff₀ hc).mpr
    norm_num at hl'
    linarith
  have hqL : 100980932337/10^10 ≤ gaussianHazard 10 := by
    change _ ≤ normalPDF 10 / normalCDF (-10)
    apply (le_div_iff₀ hc).mpr
    norm_num at hu'
    linarith
  apply abs_lt.mpr
  constructor <;> linarith

/-- The correction from a Gaussian tail ratio to the negative transport ratio. -/
theorem negative_ratio_bounds (r : ℝ) :
    (normalCDF (-r) / normalPDF r) - normalPDF r * (normalCDF (-r) / normalPDF r)^2 ≤
      transportRatio (-r) ∧ transportRatio (-r) ≤ normalCDF (-r) / normalPDF r := by
  have hs := normalCDF_pos r
  have ht := normalCDF_pos (-r)
  have hp := normalPDF_pos r
  have hsum := normalCDF_add_neg r
  have hlog1 := Real.log_le_sub_one_of_pos hs
  have hlog2 := Real.one_sub_inv_le_log_of_pos hs
  have hmul1 := mul_le_mul_of_nonneg_left hlog1 hs.le
  have hmul2 := mul_le_mul_of_nonneg_left hlog2 hs.le
  have hcancel : normalCDF r * (normalCDF r)⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
  have hnumer : normalCDF (-r) - (normalCDF (-r))^2 ≤ normalCDF r * (-Real.log (normalCDF r)) ∧
      normalCDF r * (-Real.log (normalCDF r)) ≤ normalCDF (-r) := by
    constructor <;> nlinarith
  have hk : transportRatio (-r) = normalCDF r * (-Real.log (normalCDF r)) / normalPDF r := by
    unfold transportRatio exponentialTransport gaussianHazard
    rw [neg_neg, normalPDF_neg]
    field_simp
  rw [hk]
  constructor
  · apply (le_div_iff₀ hp).mpr
    convert! hnumer.1 using 1
    field_simp
    <;> ring
  · exact (div_le_div_iff_of_pos_right hp).mpr hnumer.2

private theorem density_six_small : normalPDF 6 < 1/10^7 := by
  have h1 : Real.exp (-1) < (2/5 : ℝ) := lt_trans Real.exp_neg_one_lt_d9 (by norm_num)
  have hpow : Real.exp (-1)^18 < (2/5 : ℝ)^18 := by gcongr
  have hexp : Real.exp (-18) < 1/10^7 := by
    have he : Real.exp (-18) = Real.exp (-1)^18 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [he]
    exact lt_trans hpow (by norm_num)
  have hs : 1 ≤ Real.sqrt (2 * Real.pi) := by
    have hpi := Real.pi_gt_three
    have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
    have hs' := Real.sqrt_nonneg (2 * Real.pi)
    nlinarith
  have hspos : 0 < Real.sqrt (2 * Real.pi) := lt_of_lt_of_le zero_lt_one hs
  have hp : normalPDF 6 = Real.exp (-18) / Real.sqrt (2 * Real.pi) := by
    norm_num [normalPDF, ProbabilityTheory.gaussianPDFReal, div_eq_mul_inv]
    ring
  rw [hp, div_lt_iff₀ hspos]
  nlinarith

set_option maxRecDepth 10000 in
 theorem ratio_anchor : |transportRatio (-6) - 16237766/10^8| < 4/10^8 := by
  have hlo := mills_13_lower (x := 6) (by norm_num)
  have hhi := mills_14_upper (x := 6) (by norm_num)
  have hl : 16237765/10^8 ≤ normalCDF (-6) / normalPDF 6 := by
    apply le_trans _ hlo
    norm_num [millsPoly, millsCoeff, peval, List.range_succ]
  have hu : normalCDF (-6) / normalPDF 6 ≤ 16237767/10^8 := by
    apply le_trans hhi
    norm_num [millsPoly, millsCoeff, peval, List.range_succ]
  have h0 : 0 ≤ normalCDF (-6) / normalPDF 6 :=
    (div_pos (normalCDF_pos (-6)) (normalPDF_pos 6)).le
  have h1 : normalCDF (-6) / normalPDF 6 ≤ 1/6 := by
    have hh := mills_upper [0,1] (by decide +kernel) (x := 6) (by norm_num)
    simpa [peval] using hh
  have hsq : (normalCDF (-6) / normalPDF 6)^2 ≤ (1/6 : ℝ)^2 := by nlinarith
  have herr := mul_le_mul (density_six_small.le) hsq (sq_nonneg _)
    (show (0 : ℝ) ≤ 1/10^7 by norm_num)
  have hk := negative_ratio_bounds 6
  apply abs_lt.mpr
  constructor <;> nlinarith

end Submission.Obl.Entropy__two_eigenvalue_compact_certificate
