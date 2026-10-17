import Submission.Obl.Entropy__two_eigenvalue_negative_certificate.Coefficients

set_option maxHeartbeats 1000000

namespace Submission.Obl.Entropy__two_eigenvalue_negative_certificate

noncomputable def eta : ℝ := (40 / 37) * (7 / 25) + (42 / 37) * (3 / 4)
noncomputable def nu : ℝ := (40 / 37) * (7 / 25) ^ 2 + (45 / 37) * (3 / 4) ^ 2

lemma quadratic_box {A B C : ℝ} (hA : A ≤ 28 / 125) (hC : C ≤ 401 / 500)
    (hBl : 17 / 50 ≤ B) (hBu : B ≤ 193 / 500) (u v : ℝ) :
    A * u ^ 2 + 2 * B * u * v + C * v ^ 2 + (13 / 100) * u ^ 2 + (3 / 4) * v ^ 2 ≤
      (43 / 100) * u ^ 2 + (26 / 100) * u * v + (68 / 25) * v ^ 2 := by
  have hAu := mul_le_mul_of_nonneg_right hA (sq_nonneg u)
  have hCv := mul_le_mul_of_nonneg_right hC (sq_nonneg v)
  by_cases huv : 0 ≤ u * v
  · have hBuv := mul_le_mul_of_nonneg_right hBu huv
    nlinarith only [hAu, hCv, hBuv, sq_nonneg (u - 4 * v), sq_nonneg u, sq_nonneg v]
  · have hBuv := mul_le_mul_of_nonpos_right hBl (le_of_not_ge huv)
    nlinarith only [hAu, hCv, hBuv, le_of_not_ge huv, sq_nonneg u, sq_nonneg v]

lemma local_surplus {s k b l t : ℝ} (h : CoefficientBounds s k b l t) (u v : ℝ) :
    ((82 / 37) * b ^ 2 - eta * b + nu / 4 + (40 / 3) * l ^ 2) * u ^ 2 +
      2 * (nu / 2 - eta * b) * u * v + nu * v ^ 2 +
      dValue k b l * (eValue k b l * u + (3 / 2) * b * v) ^ 2 +
      (13 / 100) * u ^ 2 + (3 / 4) * v ^ 2 ≤
      (43 / 100) * u ^ 2 + (26 / 100) * u * v + (68 / 25) * v ^ 2 := by
  let A := (82 / 37) * b ^ 2 - eta * b + nu / 4 + (40 / 3) * l ^ 2 +
    dValue k b l * eValue k b l ^ 2
  let B := nu / 2 - eta * b + dValue k b l * eValue k b l * (3 / 2) * b
  let C := nu + dValue k b l * ((3 / 2) * b) ^ 2
  have hA : A ≤ 28 / 125 := by
    have hb2 := mul_self_le_mul_self h.basic.b_pos.le h.basic.b_le
    have hl2 := mul_self_le_mul_self h.basic.l_pos.le h.basic.l_le
    have hE2 := mul_le_mul h.de_upper h.e_le h.e_pos.le (by norm_num : (0 : ℝ) ≤ 9 / 17)
    dsimp [A, eta, nu]
    nlinarith only [hb2, hl2, hE2, h.basic.b_pos]
  have hBl : 17 / 50 ≤ B := by
    have hDEb := mul_nonneg (mul_pos h.d_pos h.e_pos).le h.basic.b_pos.le
    dsimp [B, eta, nu]
    nlinarith only [h.basic.b_le, hDEb]
  have hBu : B ≤ 193 / 500 := by
    have hDEb := mul_le_mul_of_nonneg_right h.de_upper h.basic.b_pos.le
    dsimp [B, eta, nu]
    nlinarith only [hDEb, h.basic.b_pos]
  have hC : C ≤ 401 / 500 := by
    have hDb := mul_le_mul_of_nonneg_right h.db_upper
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) h.basic.b_pos.le)
    dsimp [C, nu]
    nlinarith only [hDb, h.basic.b_le]
  convert quadratic_box hA hC hBl hBu u v using 1 <;> dsimp [A, B, C] <;> ring

end Submission.Obl.Entropy__two_eigenvalue_negative_certificate
