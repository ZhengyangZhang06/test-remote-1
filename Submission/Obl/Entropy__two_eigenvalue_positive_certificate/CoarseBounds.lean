import Submission.Obl.Entropy__two_eigenvalue_positive_certificate.DerivativeBounds

set_option maxHeartbeats 800000

open Submission.Lib.GaussianTransport

namespace Submission.Obl.Entropy__two_eigenvalue_positive_certificate

noncomputable def tailC (a : ℝ) : ℝ :=
  (tailF a - 1) / (2*tailU a) + tailF a * (tailTheta a - Real.log (tailF a))

noncomputable def tailP (a : ℝ) : ℝ :=
  transportSlope a + transportRatio a * transportCurvature a - (40/3)*(transportCurvature a)^2

lemma ratio_tailC {a : ℝ} (ha : 0 < a) :
    transportRatio a / a = 1/2 + tailU a * tailC a := by
  rw [transportRatio_tailF ha]
  dsimp [tailC, tailU]
  field_simp
  <;> ring

lemma tailC_bounds {a : ℝ} (ha : 10 ≤ a) :
    0 ≤ tailC a ∧ tailC a ≤ tailTheta a - 19/40 := by
  have hap : 0 < a := by linarith
  have hu := tailU_bounds ha
  have hFp := tailF_pos hap
  have hF := tailF_polynomial_bounds hap
  have hF0 := millsPolynomialLower_ge hu.1.le hu.2
  have hF1 := millsPolynomial_le hu.1.le hu.2
  have hL := tailF_log_bounds ha
  have ht := theta_lower ha
  have hFlo : 99/100 ≤ tailF a := by linarith
  have hFhi : tailF a ≤ 1 := by
    have hh := mul_nonneg hu.1.le (by linarith : 0 ≤ 1-3*tailU a)
    nlinarith only [hF.2, hF1, hh]
  have hlog : Real.log (tailF a) ≤ 0 := Real.log_nonpos hFp.le hFhi
  have hquot0 : -(1/2 : ℝ) ≤ (tailF a - 1)/(2*tailU a) := by
    rw [le_div_iff₀ (by exact mul_pos (by norm_num) hu.1)]
    linarith
  have hquot1 : (tailF a - 1)/(2*tailU a) ≤ -1/2+(3/2)*tailU a := by
    rw [div_le_iff₀ (by exact mul_pos (by norm_num) hu.1)]
    nlinarith only [hF.2, hF1]
  have hprod0 := mul_le_mul_of_nonneg_right hFlo (by linarith : 0 ≤ tailTheta a)
  have hprod1 := mul_le_mul_of_nonneg_right hFhi (by linarith : 0 ≤ tailTheta a)
  have hprod2 := mul_le_mul_of_nonneg_left hL.1 hFp.le
  have hprod3 := mul_le_mul_of_nonneg_right hFhi hu.1.le
  have hprod4 := mul_nonpos_of_nonneg_of_nonpos hFp.le hlog
  dsimp only [tailC]
  constructor
  · nlinarith only [hquot0, hprod0, hprod4, ht]
  · nlinarith only [hquot1, hprod1, hprod2, hprod3, hu.2]

lemma slope_scaledB {a : ℝ} (ha : 0 < a) :
    transportSlope a = 1/2-tailU a*scaledB a := by
  dsimp [tailU, scaledB]
  field_simp
  <;> ring

lemma curvature_scaledJ {a : ℝ} (ha : 0 < a) :
    transportCurvature a = scaledJ a/a^3 := by
  dsimp [scaledJ]
  field_simp

lemma curvature_deriv_scaledR {a : ℝ} (ha : 0 < a) :
    deriv transportCurvature a = -scaledR a/a^4 := by
  dsimp [scaledR]
  field_simp

/-- Coarse numerical bounds needed by the positive-tail coefficient certificate. -/
theorem coarse_bounds {a : ℝ} (ha : 10 ≤ a) :
    (241/500 ≤ transportSlope a ∧ transportSlope a < 1/2) ∧
    (0 < transportCurvature a ∧ transportCurvature a ≤ 13/5000) ∧
    (1/2 ≤ transportRatio a/a ∧ transportRatio a/a ≤ 66/125) ∧
    (493/1000 ≤ tailP a ∧ tailP a ≤ 1/2) ∧
    ((17/10)*scaledJ a ≤ scaledR a ∧ scaledR a ≤ 3*scaledJ a) ∧
    (transportCurvature a*a ≤ 13/500 ∧ 97/100 ≤ gaussianGap a*a) := by
  have hap : 0 < a := by linarith
  have hu := tailU_bounds ha
  have ht := theta_lower ha
  have hC := tailC_bounds ha
  obtain ⟨hB, hJ, hR⟩ := derivative_enclosures ha
  rw [abs_le] at hB hJ hR
  have hJp : 0 < scaledJ a := by linarith
  have hlp : 0 < transportCurvature a := by
    rw [curvature_scaledJ hap]
    exact div_pos hJp (pow_pos hap 3)
  have hbl : 241/500 ≤ transportSlope a := by
    rw [slope_scaledB hap]
    have hh := weighted_theta_bound 1 (73/50) (by norm_num) ha
    have hbu : tailU a*scaledB a ≤ (tailTheta a-73/50)/a^2 := by
      have hh' := mul_le_mul_of_nonneg_left hB.2 hu.1.le
      dsimp [tailU] at hh' ⊢
      field_simp at hh' ⊢
      nlinarith only [hh']
    norm_num at hh
    linarith
  have hlu : transportCurvature a ≤ 13/5000 := by
    rw [curvature_scaledJ hap]
    have hh := weighted_theta_bound 2 (193/100) (by norm_num) ha
    have hju : scaledJ a/a^3 ≤ 2*((tailTheta a-193/100)/a^3) := by
      apply (div_le_iff₀ (pow_pos hap 3)).2
      have hdiv : 2*((tailTheta a-193/100)/a^3)*a^3 = 2*(tailTheta a-193/100) := by field_simp
      rw [hdiv]
      linarith
    norm_num at hh
    linarith
  have hklu : 1/2 ≤ transportRatio a/a ∧ transportRatio a/a ≤ 66/125 := by
    rw [ratio_tailC hap]
    constructor
    · nlinarith only [mul_nonneg hu.1.le hC.1]
    · have hh := weighted_theta_bound 1 (19/40) (by norm_num) ha
      have hc := mul_le_mul_of_nonneg_left hC.2 hu.1.le
      have hid : tailU a*(tailTheta a-19/40) = (tailTheta a-19/40)/a^2 := by
        dsimp [tailU]; field_simp
      rw [hid] at hc
      norm_num at hh
      linarith only [hh, hc]
  have hCJ : tailU a*tailC a*scaledJ a ≤ 3/40 := by
    have hh : tailC a*scaledJ a ≤ (tailTheta a-19/40)*(2*tailTheta a-193/50) := by
      apply mul_le_mul hC.2 (by linarith only [hJ.2]) hJp.le
      linarith
    have hh' := mul_le_mul_of_nonneg_left hh hu.1.le
    have hprod := weighted_theta_product ha
    have hid : tailU a*((tailTheta a-19/40)*(2*tailTheta a-193/50)) =
        (tailTheta a-19/40)*(2*tailTheta a-193/50)/a^2 := by
      dsimp [tailU]; field_simp
    rw [hid] at hh'
    linarith only [hh', hprod]
  have hp_id : tailP a = 1/2 + tailU a *
      (-scaledB a + (1/2)*scaledJ a + tailU a*tailC a*scaledJ a) -
      (40/3)*(transportCurvature a)^2 := by
    rw [tailP, slope_scaledB hap]
    have he : transportRatio a*transportCurvature a =
        tailU a*(1/2+tailU a*tailC a)*scaledJ a := by
      have hr := ratio_tailC hap
      rw [curvature_scaledJ hap]
      dsimp [tailU] at hr ⊢
      field_simp at hr ⊢
      nlinarith only [hr]
    rw [he]
    ring
  have hp_bounds : 493/1000 ≤ tailP a ∧ tailP a ≤ 1/2 := by
    have hcore0 : -(61/100 : ℝ) ≤ -scaledB a+(1/2)*scaledJ a := by linarith
    have hcore1 : -scaledB a+(1/2)*scaledJ a ≤ -(39/100 : ℝ) := by linarith
    have hCJ0 : 0 ≤ tailU a*tailC a*scaledJ a :=
      mul_nonneg (mul_nonneg hu.1.le hC.1) hJp.le
    have hl2 : (transportCurvature a)^2 ≤ (13/5000 : ℝ)^2 := by nlinarith only [hlp, hlu]
    have h0 := mul_le_mul_of_nonneg_left hcore0 hu.1.le
    have h1 := mul_le_mul_of_nonneg_left (show
        -scaledB a+(1/2)*scaledJ a+tailU a*tailC a*scaledJ a ≤ 0 by linarith) hu.1.le
    have h2 := mul_nonneg hu.1.le hCJ0
    rw [hp_id]
    constructor
    · nlinarith only [h0, h2, hu.2, hl2]
    · nlinarith only [h1, sq_nonneg (transportCurvature a)]
  have hrj : (17/10)*scaledJ a ≤ scaledR a ∧ scaledR a ≤ 3*scaledJ a := by
    constructor <;> linarith
  have hla : transportCurvature a*a ≤ 13/500 := by
    have hh := weighted_theta_bound 1 (193/100) (by norm_num) ha
    have he : transportCurvature a*a = scaledJ a/a^2 := by
      rw [curvature_scaledJ hap]; field_simp
    rw [he]
    have hh' : scaledJ a/a^2 ≤ 2*((tailTheta a-193/100)/a^2) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by linarith only [hJ.2]) (sq_nonneg a)
    norm_num at hh
    linarith only [hh, hh']
  have hda : 97/100 ≤ gaussianGap a*a := by
    have hH := (tailF_inverse_bounds ha).1
    have hpoly : 1+(97/100)*tailU a ≤ hazardPolynomial (tailU a) := by
      have h0 := mul_nonneg hu.1.le (by linarith : 0 ≤ (3/100:ℝ)-2*tailU a)
      have h1 := mul_nonneg (pow_nonneg hu.1.le 3) (by linarith : 0 ≤ (10:ℝ)-74*tailU a)
      dsimp [hazardPolynomial]
      nlinarith only [h0, h1]
    have hh := mul_le_mul_of_nonneg_right (hpoly.trans hH) (sq_nonneg a)
    rw [gaussianGap, gaussianHazard_tailF hap]
    have hu_id : tailU a*a^2 = 1 := by dsimp [tailU]; field_simp
    nlinarith only [hh, hu_id]
  exact ⟨⟨hbl, transportSlope_lt_half a⟩, ⟨hlp, hlu⟩, hklu, hp_bounds, hrj, hla, hda⟩

end Submission.Obl.Entropy__two_eigenvalue_positive_certificate
