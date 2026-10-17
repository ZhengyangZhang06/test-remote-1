import Submission.Obl.Entropy__two_eigenvalue_positive_certificate.TailModel
import Submission.Obl.Entropy__two_eigenvalue_positive_certificate.Errors

open Submission.Lib.GaussianTransport

namespace Submission.Obl.Entropy__two_eigenvalue_positive_certificate

noncomputable def scaledB (a : ℝ) : ℝ := (1/2 - transportSlope a) * a^2
noncomputable def scaledJ (a : ℝ) : ℝ := transportCurvature a * a^3
noncomputable def scaledR (a : ℝ) : ℝ := -deriv transportCurvature a * a^4

/-- The actual derivatives have the uniform enclosures of the tail calculation. -/
theorem derivative_enclosures {a : ℝ} (ha : 10 ≤ a) :
    |scaledB a - (tailTheta a - 3/2)| ≤ 1/25 ∧
    |scaledJ a - (2*tailTheta a - 4)| ≤ 7/50 ∧
    |scaledR a - (6*tailTheta a - 14)| ≤ 9/10 := by
  have hap : 0 < a := by linarith
  let u := tailU a
  let t := tailTheta a
  let F := tailF a
  let H := (tailF a)⁻¹
  let T := tailTheta a - Real.log (tailF a)
  have hu : 0 < u := (tailU_bounds ha).1
  have hu1 : u ≤ 1/100 := (tailU_bounds ha).2
  have ht : 3221/1000 ≤ t := theta_lower ha
  obtain ⟨e, h, s, he, hh, hs, hF, hH, hL⟩ := tail_remainder_parameters ha
  have hh0 : 0 ≤ h := by
    have hHp := (tailF_inverse_bounds ha).1
    rw [hH] at hHp
    have hmul : 0 ≤ h * (tailU a)^5 := by linarith
    exact (mul_nonneg_iff_of_pos_right (pow_pos hu 5)).mp hmul
  have hT : t + u + s*u^2 = T := by dsimp [u, t, T]; linarith only [hL]
  have hid := tail_polynomial_identities hu.ne' t e h s
  dsimp only at hid
  rw [← hF, ← hH, hT] at hid
  rcases hid with ⟨hB, hJ, hR⟩
  have hF0 : F ≠ 0 := (tailF_pos hap).ne'
  have hq : gaussianHazard a = a * H := gaussianHazard_tailF hap
  have hk : transportRatio a = a * F / 2 + F*T/a := transportRatio_tailF hap
  have hb : transportSlope a = 1 - ((1-F)/(2*u) + (1-F)*T) := by
    rw [transportSlope, gaussianGap, hq, hk]
    dsimp only [u, tailU, H]
    change 1 - (a * F / 2 + F * T / a) * (a * F⁻¹ - a) = _
    field_simp
    <;> ring
  have hbe : transportSlope a = 1/2-u*tailB u t e h s := by rw [hb, hB]; ring
  have hl : transportCurvature a = a *
      (1 + F/2 - H - (1-F)/(2*u) + ((1+u)*F-1)*T) := by
    rw [transportCurvature, hk, hq, hb]
    dsimp only [u, tailU]
    field_simp
    <;> ring
  have hle : transportCurvature a = tailJ u t e h s / a^3 := by
    rw [hl, hJ]
    dsimp only [u, tailU]
    field_simp
    <;> ring
  have hre : deriv transportCurvature a = -tailR u t e h s / a^4 := by
    have hd := (hasDerivAt_transportCurvature a).deriv
    rw [gaussianGap, hq, hbe, hle] at hd
    have hh' : deriv transportCurvature a =
        2*(1/2-u*tailB u t e h s) - (H^2-H)/u + u*tailJ u t e h s := by
      rw [hd]
      dsimp only [u, tailU]
      field_simp
      <;> ring
    have hr' : deriv transportCurvature a = -(u^2*tailR u t e h s) := by
      linarith only [hh', hR]
    rw [hr']
    dsimp only [u, tailU]
    field_simp
  have hw : |u*t| ≤ 1611/50000 := by
    rw [abs_of_nonneg (mul_nonneg hu.le (by linarith))]
    have hw := weighted_theta_bound 1 0 (by norm_num) ha
    convert! hw using 1 <;> dsimp [u, t, tailU] <;> field_simp <;> ring
  have hw1 : u*(t-2721/1000) ≤ 501/100000 := by
    have hw := weighted_theta_bound 1 (2721/1000) (by norm_num) ha
    convert! hw using 1 <;> dsimp [u, t, tailU] <;> field_simp <;> ring
  have hw2 : u^2*(t-2971/1000) ≤ 251/10000000 := by
    have hw := weighted_theta_bound 3 (2971/1000) (by norm_num) ha
    convert! hw using 1 <;> dsimp [u, t, tailU] <;> field_simp <;> ring
  have herrors := tail_BJR_errors hu.le hu1 ht hw hw1 hw2 he hh0
    ((le_abs_self h).trans hh) hs
  have heB : scaledB a = tailB u t e h s := by
    rw [scaledB, hbe]
    dsimp only [u, tailU]
    field_simp
    <;> ring
  have heJ : scaledJ a = tailJ u t e h s := by rw [scaledJ, hle]; field_simp
  have heR : scaledR a = tailR u t e h s := by rw [scaledR, hre]; field_simp
  rwa [heB, heJ, heR]

end Submission.Obl.Entropy__two_eigenvalue_positive_certificate
