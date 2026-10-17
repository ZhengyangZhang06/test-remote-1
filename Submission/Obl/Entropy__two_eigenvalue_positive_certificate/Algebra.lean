import Mathlib

set_option maxHeartbeats 800000

namespace Submission.Obl.Entropy__two_eigenvalue_positive_certificate

/-- The coarse positive-tail bounds imply the coefficient table and the local surplus. -/
theorem tail_algebra {b l p : ℝ}
    (hb0 : 241 / 500 ≤ b) (hb1 : b ≤ 1 / 2)
    (hl0 : 0 ≤ l) (hl1 : l ≤ 13 / 5000)
    (hp0 : 493 / 1000 ≤ p) (hp1 : p ≤ 1 / 2) :
    let D := (5 / 17) / p
    let E := p - b ^ 2 - (40 / 3) * l ^ 2 + (3 / 4) * b
    let eta := (40 / 37) * (7 / 25) + (42 / 37) * (3 / 4)
    let nu := (40 / 37) * (7 / 25) ^ 2 + (45 / 37) * (3 / 4) ^ 2
    (89 / 200 ≤ b ∧ b ≤ 1 / 2 ∧ (40 / 3) * l ≤ 1 / 5 ∧
      D ≤ 16 / 25 ∧ 8 / 25 ≤ D * E ∧ D * E ≤ 2 / 5 ∧
      D * (3 / 2) * b ≤ 12 / 25) ∧
    (∀ u v : ℝ,
      ((82 / 37) * b ^ 2 - eta * b + nu / 4 + (40 / 3) * l ^ 2) * u ^ 2 +
      2 * (nu / 2 - eta * b) * u * v + nu * v ^ 2 +
      D * (E * u + (3 / 2) * b * v) ^ 2 + (11 / 500) * u ^ 2 +
      (3 / 4) * v ^ 2 ≤ (43 / 100) * u ^ 2 + (26 / 100) * u * v +
      (68 / 25) * v ^ 2) := by
  dsimp only
  have hp : 0 < p := by linarith
  have hb : 0 ≤ b := by linarith
  have hl2 : l ^ 2 ≤ (13 / 5000 : ℝ) ^ 2 := by nlinarith
  let E := p - b ^ 2 - (40 / 3) * l ^ 2 + (3 / 4) * b
  let D := (5 / 17) / p
  have hD0 : 0 ≤ D := le_of_lt (div_pos (by norm_num) hp)
  have hDp : D * p = 5 / 17 := by dsimp [D]; field_simp
  have hD1 : D ≤ 600 / 1000 := by
    dsimp [D]
    apply (div_le_iff₀ hp).2
    linarith
  have hv0 : (1 / 8 : ℝ) ≤ b * (3 / 4 - b) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb1) (by linarith : 0 ≤ b - 1 / 4)]
  have hv1 : b * (3 / 4 - b) ≤ (241 / 500 : ℝ) * (3 / 4 - 241 / 500) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb0) (by linarith : 0 ≤ b + 241 / 500 - 3 / 4)]
  have hE0 : 0 ≤ E := by dsimp [E]; nlinarith
  have hE1 : E ≤ p + (241 / 500 : ℝ) * (3 / 4 - 241 / 500) := by
    dsimp [E]; nlinarith [sq_nonneg l]
  have hK0 : 367 / 1000 ≤ D * E := by
    have h : (367 / 1000 : ℝ) * p ≤ (5 / 17) * E := by
      dsimp [E]
      nlinarith
    calc
      _ = D * ((367 / 1000) * p) / (5 / 17) := by rw [← mul_assoc, mul_comm D, mul_assoc, hDp]; ring
      _ ≤ D * ((5 / 17) * E) / (5 / 17) := by gcongr
      _ = _ := by ring
  have hK1 : D * E ≤ 2 / 5 := by
    have h : (5 / 17) * E ≤ (2 / 5 : ℝ) * p := by nlinarith
    have hh := mul_le_mul_of_nonneg_left h hD0
    nlinarith [hDp]
  have hEE : D * E ^ 2 ≤ (5 / 17 : ℝ) * (1 / 2 + (241 / 500) * (3 / 4 - 241 / 500)) ^ 2 / (1 / 2) := by
    have hsq : E ^ 2 ≤ (p + (241 / 500 : ℝ) * (3 / 4 - 241 / 500)) ^ 2 := by
      nlinarith
    have hpoly : (5 / 17) * E ^ 2 ≤
        ((5 / 17 : ℝ) * (1 / 2 + (241 / 500) * (3 / 4 - 241 / 500)) ^ 2 / (1 / 2)) * p := by
      have hh := mul_nonneg (sub_nonneg.mpr hp1)
        (by linarith : 0 ≤ p - 2 * ((241 / 500 : ℝ) * (3 / 4 - 241 / 500)) ^ 2)
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hpoly hD0
    nlinarith [hDp]
  have hN11 : (82 / 37) * b ^ 2 -
      ((40 / 37) * (7 / 25) + (42 / 37) * (3 / 4)) * b +
      ((40 / 37) * (7 / 25) ^ 2 + (45 / 37) * (3 / 4) ^ 2) / 4 +
      (40 / 3) * l ^ 2 + D * E ^ 2 ≤ 403 / 1000 := by
    have hh := mul_nonneg (sub_nonneg.mpr hb1)
      (by linarith : 0 ≤ (82 / 37 : ℝ) * (b + 1 / 2) -
        ((40 / 37) * (7 / 25) + (42 / 37) * (3 / 4)))
    nlinarith
  have hN22 : ((40 / 37 : ℝ) * (7 / 25) ^ 2 + (45 / 37) * (3 / 4) ^ 2) +
      D * ((3 / 2) * b) ^ 2 ≤ 28 / 25 := by
    have hh : ((3 / 2) * b) ^ 2 ≤ (3 / 4 : ℝ) ^ 2 := by nlinarith only [hb1, hb, sq_nonneg b]
    have hh' := mul_le_mul_of_nonneg_left hh hD0
    nlinarith only [hh', hD1]
  have hN12 : 2 / 25 ≤
      ((40 / 37 : ℝ) * (7 / 25) ^ 2 + (45 / 37) * (3 / 4) ^ 2) / 2 -
        ((40 / 37) * (7 / 25) + (42 / 37) * (3 / 4)) * b + D * E * ((3 / 2) * b) ∧
      ((40 / 37 : ℝ) * (7 / 25) ^ 2 + (45 / 37) * (3 / 4) ^ 2) / 2 -
        ((40 / 37) * (7 / 25) + (42 / 37) * (3 / 4)) * b + D * E * ((3 / 2) * b) ≤ 13 / 100 := by
    constructor
    · have hh := mul_le_mul_of_nonneg_right hK0 hb
      nlinarith only [hh, hb1]
    · have hh := mul_le_mul_of_nonneg_right hK1 hb
      nlinarith only [hh, hb0]
  constructor
  · refine ⟨by linarith, hb1, by linarith, by dsimp [D] at *; linarith,
      by change 8 / 25 ≤ D * E; linarith only [hK0], hK1, ?_⟩
    have hh := mul_le_mul_of_nonneg_left hb1 hD0
    nlinarith only [hh, hD1]
  · intro u v
    have h1 := mul_le_mul_of_nonneg_right hN11 (sq_nonneg u)
    have h2 := mul_le_mul_of_nonneg_right hN22 (sq_nonneg v)
    have h3 : (2 * (((40 / 37 : ℝ) * (7 / 25) ^ 2 + (45 / 37) * (3 / 4) ^ 2) / 2 -
        ((40 / 37) * (7 / 25) + (42 / 37) * (3 / 4)) * b + D * E * ((3 / 2) * b)) -
        26 / 100) * u * v ≤ (1 / 10 : ℝ) * |u * v| := by
      rcases le_total 0 (u * v) with huv | huv
      · rw [abs_of_nonneg huv]
        have hh := mul_le_mul_of_nonneg_right hN12.2 huv
        nlinarith only [hh, huv]
      · rw [abs_of_nonpos huv]
        have hh := mul_le_mul_of_nonpos_right hN12.1 huv
        nlinarith only [hh]
    have h4 : (1 / 10 : ℝ) * |u * v| ≤ (1 / 200 : ℝ) * u ^ 2 + (1 / 2 : ℝ) * v ^ 2 := by
      rw [abs_mul]
      nlinarith only [sq_nonneg (|u| - 10 * |v|), sq_abs u, sq_abs v]
    change _ ≤ _
    dsimp only [D, E] at h1 h2 h3
    nlinarith only [h1, h2, h3, h4, sq_nonneg v]

end Submission.Obl.Entropy__two_eigenvalue_positive_certificate
