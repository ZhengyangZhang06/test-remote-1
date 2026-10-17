import Mathlib

set_option maxHeartbeats 1000000

namespace Submission.Obl.Entropy__two_eigenvalue_negative_certificate

/-- Rational bounds after the substitution `s = 1/r`. -/
structure TailData (s k b l t : ℝ) : Prop where
  s_pos : 0 < s
  s_le : s ≤ 1 / 6
  k_pos : 0 < k
  k_le : k ≤ s
  b_lower : s ^ 2 - (301 / 100) * s ^ 4 ≤ b
  b_upper : b ≤ s ^ 2 + (1 / 100) * s ^ 4
  l_lower : 2 * s ^ 3 - (601 / 50) * s ^ 5 ≤ l
  l_upper : l ≤ 2 * s ^ 3 + (1 / 50) * s ^ 5
  t_lower : 6 * s ^ 4 - (3003 / 50) * s ^ 6 ≤ t
  t_upper : t ≤ 6 * s ^ 4 + (3 / 50) * s ^ 6

structure TailEstimates (s k b l t : ℝ) : Prop where
  b_pos : 0 < b
  b_le : b ≤ 7 / 250
  l_pos : 0 < l
  l_le : l ≤ 1 / 100
  t_pos : 0 < t
  t_le : t ≤ (61 / 100) * l
  kl_le : k * l ≤ (7 / 100) * b
  ll_le : (40 / 3) * l ^ 2 ≤ b / 21
  p_lower : s ^ 2 - (9 / 2) * s ^ 4 ≤ b + k * l - (40 / 3) * l ^ 2

lemma tail_estimates {s k b l t : ℝ} (h : TailData s k b l t) : TailEstimates s k b l t := by
  have hs := h.s_pos
  have hs6 := h.s_le
  have hs2 : s ^ 2 ≤ 1 / 36 := by nlinarith only [hs, hs6]
  have hs3 : s ^ 3 ≤ 1 / 216 := by
    nlinarith only [mul_le_mul hs2 hs6 hs.le (by norm_num : (0 : ℝ) ≤ 1 / 36)]
  have hs4 : s ^ 4 ≤ s ^ 2 / 36 := by
    nlinarith only [mul_le_mul_of_nonneg_right hs2 (sq_nonneg s)]
  have hs5 : s ^ 5 ≤ s ^ 3 / 36 := by
    nlinarith only [mul_le_mul_of_nonneg_right hs2 (by positivity : 0 ≤ s ^ 3)]
  have hs6' : s ^ 6 ≤ s ^ 4 / 36 := by
    nlinarith only [mul_le_mul_of_nonneg_right hs2 (by positivity : 0 ≤ s ^ 4)]
  have hbl : (9 / 10) * s ^ 2 ≤ b := by
    nlinarith only [h.b_lower, hs4, sq_nonneg s]
  have hbu : b ≤ (1001 / 1000) * s ^ 2 := by
    nlinarith only [h.b_upper, hs4, sq_nonneg s]
  have hll : (83 / 50) * s ^ 3 ≤ l := by
    nlinarith only [h.l_lower, hs5, pow_nonneg hs.le 3]
  have hlu : l ≤ (1001 / 500) * s ^ 3 := by
    nlinarith only [h.l_upper, hs5, pow_nonneg hs.le 3]
  have htl : 4 * s ^ 4 ≤ t := by
    nlinarith only [h.t_lower, hs6', pow_nonneg hs.le 4]
  have htu : t ≤ (3003 / 500) * s ^ 4 := by
    nlinarith only [h.t_upper, hs6', pow_nonneg hs.le 4]
  have hbpos : 0 < b := lt_of_lt_of_le (by positivity) hbl
  have hlpos : 0 < l := lt_of_lt_of_le (by positivity) hll
  have hl2 : l ^ 2 ≤ (1001 / 500 : ℝ) ^ 2 * s ^ 6 := by
    nlinarith only [mul_self_le_mul_self hlpos.le hlu]
  have hs6sq : s ^ 6 ≤ s ^ 2 / 1296 := by
    nlinarith only [hs6', hs4]
  have hkl : k * l ≤ (1001 / 500) * s ^ 4 := by
    nlinarith only [mul_le_mul h.k_le hlu hlpos.le hs.le]
  refine ⟨hbpos, ?_, hlpos, ?_, lt_of_lt_of_le (by positivity) htl, ?_, ?_, ?_, ?_⟩
  · nlinarith only [hbu, hs2]
  · nlinarith only [hlu, hs3]
  · have hs4s3 : s ^ 4 ≤ s ^ 3 / 6 := by
      nlinarith only [mul_le_mul_of_nonneg_right hs6 (by positivity : 0 ≤ s ^ 3)]
    nlinarith only [htu, hs4s3, hll, pow_nonneg hs.le 3]
  · nlinarith only [hkl, hs4, hbl, sq_nonneg s]
  · nlinarith only [hl2, hs6sq, hbl, sq_nonneg s]
  · nlinarith only [h.b_lower, hl2, hs6', mul_nonneg h.k_pos.le hlpos.le,
      pow_nonneg hs.le 4]

end Submission.Obl.Entropy__two_eigenvalue_negative_certificate
