import Submission.Obl.Entropy__two_eigenvalue_negative_certificate.Rational

set_option maxHeartbeats 1000000

namespace Submission.Obl.Entropy__two_eigenvalue_negative_certificate

noncomputable def pValue (k b l : ℝ) : ℝ := b + k * l - (40 / 3) * l ^ 2

noncomputable def eValue (k b l : ℝ) : ℝ := pValue k b l + b * (3 / 4 - b) - (40 / 3) * l ^ 2

noncomputable def dValue (k b l : ℝ) : ℝ := (5 / 17) / pValue k b l

structure CoefficientBounds (s k b l t : ℝ) : Prop where
  basic : TailEstimates s k b l t
  p_pos : 0 < pValue k b l
  p_lower : (20 / 21) * b ≤ pValue k b l
  p_upper : pValue k b l ≤ (107 / 100) * b
  p_tail : s ^ 2 ≤ pValue k b l * (1 + 7 * s ^ 2)
  e_pos : 0 < eValue k b l
  e_le : eValue k b l ≤ 13 / 250
  d_pos : 0 < dValue k b l
  dp : dValue k b l * pValue k b l = 5 / 17
  de_lower : 15 / 34 ≤ dValue k b l * eValue k b l
  de_upper : dValue k b l * eValue k b l ≤ 9 / 17
  db_upper : dValue k b l * (3 / 2) * b ≤ 1 / 2

lemma coefficient_bounds {s k b l t : ℝ} (h : TailData s k b l t) :
    CoefficientBounds s k b l t := by
  have he := tail_estimates h
  have hs := h.s_pos
  have hs2 : s ^ 2 ≤ 1 / 36 := by nlinarith only [hs, h.s_le]
  have hklpos := mul_pos h.k_pos he.l_pos
  have hpL : (20 / 21) * b ≤ pValue k b l := by
    dsimp [pValue]
    nlinarith only [he.ll_le, hklpos]
  have hpU : pValue k b l ≤ (107 / 100) * b := by
    dsimp [pValue]
    nlinarith only [he.kl_le, sq_nonneg l]
  have hp : 0 < pValue k b l := lt_of_lt_of_le (by nlinarith only [he.b_pos]) hpL
  have hpT : s ^ 2 ≤ pValue k b l * (1 + 7 * s ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_right he.p_lower
      (by positivity : 0 ≤ 1 + 7 * s ^ 2)
    have h2 := mul_nonneg (pow_nonneg hs.le 4)
      (show 0 ≤ 5 / 2 - (63 / 2) * s ^ 2 by nlinarith only [hs2])
    dsimp [pValue]
    nlinarith only [h1, h2]
  have hbb : b ^ 2 ≤ (7 / 250) * b := by
    nlinarith only [mul_le_mul_of_nonneg_right he.b_le he.b_pos.le]
  have hEL : (3 / 2) * pValue k b l ≤ eValue k b l := by
    dsimp only [eValue]
    nlinarith only [hpU, he.ll_le, hbb, he.b_pos]
  have hEU : eValue k b l ≤ (9 / 5) * pValue k b l := by
    dsimp only [eValue]
    nlinarith only [hpL, hp, sq_nonneg b, sq_nonneg l]
  have hE : 0 < eValue k b l := lt_of_lt_of_le (by positivity) hEL
  have hEc : eValue k b l ≤ 13 / 250 := by
    dsimp [eValue, pValue]
    nlinarith only [he.kl_le, he.b_le, sq_nonneg b, sq_nonneg l]
  have hD : 0 < dValue k b l := div_pos (by norm_num) hp
  have hDp : dValue k b l * pValue k b l = 5 / 17 := div_mul_cancel₀ _ hp.ne'
  have hDEl : 15 / 34 ≤ dValue k b l * eValue k b l := by
    nlinarith only [mul_le_mul_of_nonneg_left hEL hD.le, hDp]
  have hDEu : dValue k b l * eValue k b l ≤ 9 / 17 := by
    nlinarith only [mul_le_mul_of_nonneg_left hEU hD.le, hDp]
  have hDB : dValue k b l * (3 / 2) * b ≤ 1 / 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hpL hD.le, hDp]
  exact ⟨he, hp, hpL, hpU, hpT, hE, hEc, hD, hDp, hDEl, hDEu, hDB⟩

end Submission.Obl.Entropy__two_eigenvalue_negative_certificate
