import Submission.Obl.Entropy__two_eigenvalue_positive_certificate.Mills
import Submission.Obl.Entropy__two_eigenvalue_positive_certificate.LogBounds
import Submission.Obl.Entropy__two_eigenvalue_positive_certificate.PolynomialBounds
import Submission.Lib.GaussianTransport.GaussianSlope

open Submission.Lib.GaussianTransport

namespace Submission.Obl.Entropy__two_eigenvalue_positive_certificate

noncomputable def tailU (a : ℝ) : ℝ := (a⁻¹)^2
noncomputable def tailF (a : ℝ) : ℝ := a * normalCDF (-a) / normalPDF a

lemma tailU_bounds {a : ℝ} (ha : 10 ≤ a) : 0 < tailU a ∧ tailU a ≤ 1 / 100 := by
  have hap : 0 < a := by linarith
  have hai : 0 < a⁻¹ := inv_pos.2 hap
  have h : a⁻¹ ≤ (1 / 10 : ℝ) := by rw [inv_le_comm₀ hap (by norm_num)]; norm_num; exact ha
  dsimp [tailU]
  constructor
  · positivity
  · nlinarith

lemma tailF_pos {a : ℝ} (ha : 0 < a) : 0 < tailF a :=
  div_pos (mul_pos ha (normalCDF_pos (-a))) (normalPDF_pos a)

lemma tailF_polynomial_bounds {a : ℝ} (ha : 0 < a) :
    millsPolynomialLower (tailU a) ≤ tailF a ∧
    tailF a ≤ millsPolynomial (tailU a) := by
  have h := mills_bounds_high ha
  have h0 := mul_le_mul_of_nonneg_left h.1 ha.le
  have h1 := mul_le_mul_of_nonneg_left h.2 ha.le
  have he0 : a * (normalPDF a * millsLower8 a) =
      millsPolynomialLower (tailU a) * normalPDF a := by
    dsimp [millsPolynomialLower, tailU, millsLower8, millsUpper7, millsLower, millsUpper]
    field_simp
    <;> ring
  have he1 : a * (normalPDF a * millsUpper7 a) =
      millsPolynomial (tailU a) * normalPDF a := by
    dsimp [millsPolynomial, tailU, millsUpper7, millsLower, millsUpper]
    field_simp
    <;> ring
  constructor
  · apply (le_div_iff₀ (normalPDF_pos a)).2
    rwa [he0] at h0
  · apply (div_le_iff₀ (normalPDF_pos a)).2
    rwa [he1] at h1

lemma tailF_inverse_bounds {a : ℝ} (ha : 10 ≤ a) :
    hazardPolynomial (tailU a) ≤ (tailF a)⁻¹ ∧
    (tailF a)⁻¹ ≤ hazardPolynomialUpper (tailU a) := by
  have hu := tailU_bounds ha
  have hF := tailF_polynomial_bounds (by linarith : 0 < a)
  have hFp := tailF_pos (by linarith : 0 < a)
  have hp := hazardPolynomial_nonneg hu.1.le hu.2
  have hp' : 0 ≤ hazardPolynomialUpper (tailU a) := by
    dsimp [hazardPolynomialUpper, hazardPolynomial] at *
    nlinarith [pow_nonneg hu.1.le 5]
  constructor
  · rw [inv_eq_one_div, le_div_iff₀ hFp]
    calc
      _ ≤ hazardPolynomial (tailU a) * millsPolynomial (tailU a) :=
        mul_le_mul_of_nonneg_left hF.2 hp
      _ ≤ 1 := by simpa [mul_comm] using mills_hazard_lower hu.1.le hu.2
  · rw [inv_eq_one_div, div_le_iff₀ hFp]
    calc
      1 ≤ hazardPolynomialUpper (tailU a) * millsPolynomialLower (tailU a) :=
        by simpa [mul_comm] using mills_hazard_upper hu.1.le hu.2
      _ ≤ _ := mul_le_mul_of_nonneg_left hF.1 hp'

lemma tailF_log_bounds {a : ℝ} (ha : 10 ≤ a) :
    -tailU a ≤ Real.log (tailF a) ∧
    Real.log (tailF a) ≤ -tailU a + 3 * (tailU a)^2 := by
  have hu := tailU_bounds ha
  have hF := tailF_polynomial_bounds (by linarith : 0 < a)
  have hFp := tailF_pos (by linarith : 0 < a)
  have hH := tailF_inverse_bounds ha
  have hH1 := hazardPolynomialUpper_le hu.1.le hu.2
  have hF1 := millsPolynomial_le hu.1.le hu.2
  constructor
  · linarith [Real.one_sub_inv_le_log_of_pos hFp]
  · linarith [Real.log_le_sub_one_of_pos hFp]

/-- Bounded remainder parameters in the tail expansions. -/
lemma tail_remainder_parameters {a : ℝ} (ha : 10 ≤ a) :
    ∃ e h s : ℝ, |e| ≤ 135135 ∧ |h| ≤ 706 ∧ |s| ≤ 3 ∧
      tailF a = millsPolynomial (tailU a) + e * (tailU a)^7 ∧
      (tailF a)⁻¹ = hazardPolynomial (tailU a) + h * (tailU a)^5 ∧
      -Real.log (tailF a) = tailU a + s * (tailU a)^2 := by
  have hu := (tailU_bounds ha).1
  have hF := tailF_polynomial_bounds (by linarith : 0 < a)
  have hH := tailF_inverse_bounds ha
  have hL := tailF_log_bounds ha
  refine ⟨(tailF a - millsPolynomial (tailU a)) / (tailU a)^7,
    ((tailF a)⁻¹ - hazardPolynomial (tailU a)) / (tailU a)^5,
    (-Real.log (tailF a) - tailU a) / (tailU a)^2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_le, le_div_iff₀ (pow_pos hu 7), div_le_iff₀ (pow_pos hu 7)]
    dsimp [millsPolynomialLower, millsPolynomial] at *
    constructor <;> nlinarith only [hF.1, hF.2, pow_nonneg hu.le 7]
  · rw [abs_le, le_div_iff₀ (pow_pos hu 5), div_le_iff₀ (pow_pos hu 5)]
    dsimp [hazardPolynomialUpper, hazardPolynomial] at *
    constructor <;> nlinarith only [hH.1, hH.2, pow_nonneg hu.le 5]
  · rw [abs_le, le_div_iff₀ (pow_pos hu 2), div_le_iff₀ (pow_pos hu 2)]
    constructor <;> nlinarith only [hL.1, hL.2, sq_nonneg (tailU a)]
  all_goals field_simp; ring

lemma hasDerivAt_transportCurvature (a : ℝ) :
    HasDerivAt transportCurvature
      (2 * transportSlope a - gaussianHazard a * gaussianGap a + a * transportCurvature a) a := by
  convert! ((hasDerivAt_transportRatio a).sub (hasDerivAt_gaussianHazard a)).add
    ((hasDerivAt_id a).mul (hasDerivAt_transportSlope a)) using 1
  simp only [id_eq, one_mul, gaussianGap]
  ring

lemma transport_log_identity {a : ℝ} (ha : 0 < a) :
    exponentialTransport a = a ^ 2 / 2 + tailTheta a - Real.log (tailF a) := by
  have hsp : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hpdf : Real.log (normalPDF a) = -Real.log (Real.sqrt (2 * Real.pi)) - a^2/2 := by
    simp only [normalPDF, ProbabilityTheory.gaussianPDFReal, NNReal.coe_one, sub_zero,
      mul_one, Real.log_mul (inv_ne_zero hsp.ne') (Real.exp_ne_zero _),
      Real.log_inv, Real.log_exp]
    ring
  dsimp [tailF, tailTheta, exponentialTransport]
  rw [Real.log_div (mul_ne_zero ha.ne' (normalCDF_pos (-a)).ne') (normalPDF_pos a).ne',
    Real.log_mul ha.ne' (normalCDF_pos (-a)).ne', Real.log_mul ha.ne' hsp.ne', hpdf]
  ring

lemma gaussianHazard_tailF {a : ℝ} (ha : 0 < a) :
    gaussianHazard a = a * (tailF a)⁻¹ := by
  dsimp [gaussianHazard, tailF]
  field_simp

lemma transportRatio_tailF {a : ℝ} (ha : 0 < a) :
    transportRatio a = a * tailF a / 2 +
      tailF a * (tailTheta a - Real.log (tailF a)) / a := by
  rw [transportRatio, transport_log_identity ha, gaussianHazard_tailF ha]
  field_simp
  <;> ring

end Submission.Obl.Entropy__two_eigenvalue_positive_certificate
