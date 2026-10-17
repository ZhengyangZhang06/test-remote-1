import Submission.Obl.Entropy__hazard_secant_surplus.ExponentialAverages

open MeasureTheory Set

namespace Submission.Obl.Entropy__hazard_secant_surplus

lemma algebraic_average_surplus {D B L C S R m : ℝ}
    (hD : 0 < D) (hB : 0 ≤ B) (hBD : B ≤ D / 2) (hS : 1 ≤ S) (hm : 0 ≤ m)
    (hL : D ^ 2 - B ^ 2 ≤ L) (hC : R * L ≤ C)
    (hR : 1 + m * (1 - 1 / S) ≤ R) :
    1 - (B / D) ^ 2 + (3 / 4 : ℝ) * (1 + m) * (S - 1) ≤ S * C / D ^ 2 := by
  have hSpos : 0 < S := by linarith
  have hLbound : (3 / 4 : ℝ) * D ^ 2 ≤ L := by nlinarith
  have hL0 : 0 ≤ L := by nlinarith
  have hR' : 1 + (1 + m) * (S - 1) ≤ S * R := by
    have hh := mul_le_mul_of_nonneg_left hR hSpos.le
    field_simp [ne_of_gt hSpos] at hh
    nlinarith
  have hCL : (1 + (1 + m) * (S - 1)) * L ≤ S * C := by
    have h1 := mul_le_mul_of_nonneg_right hR' hL0
    have h2 := mul_le_mul_of_nonneg_left hC hSpos.le
    nlinarith
  have hextra := mul_le_mul_of_nonneg_left hLbound
    (show 0 ≤ (1 + m) * (S - 1) by positivity)
  apply (le_div_iff₀ (sq_pos_of_pos hD)).mpr
  simp only [div_pow]
  field_simp [ne_of_gt hD]
  nlinarith

open Submission.Lib.GaussianTransport

lemma secant_surplus_of_lt (h : GrowthCertificate) {a b : ℝ} (hab : a < b) :
    1 - dividedDifference transportRatio a b ^ 2 + surplus a b ≤
      dividedDifference gaussianHazard a b ^ 2 * arithmeticMean a b /
        (gaussianHazard a * gaussianHazard b) := by
  let δ := Real.log (gaussianHazard b) - Real.log (gaussianHazard a)
  let x := δ / 2
  let D := (b - a) / δ
  let B := (transportRatio b - transportRatio a) / δ
  let L := (∫ s in Real.log (gaussianHazard a)..Real.log (gaussianHazard b), logM s) / δ
  let S := sinhc x ^ 2
  let R := sinhc ((1 + growthStep a) * x) / (sinhc x * sinhc (growthStep a * x))
  have hδ : 0 < δ := sub_pos.mpr (log_interval_lt hab)
  have hx : 0 < x := by dsimp [x]; positivity
  have hD : 0 < D := div_pos (sub_pos.mpr hab) hδ
  have hB : 0 ≤ B := div_nonneg (ratio_increment_bounds hab).1 hδ.le
  have hBD : B ≤ D / 2 := by
    have hh := div_le_div_of_nonneg_right (ratio_increment_bounds hab).2 hδ.le
    simpa only [B, D, div_div, mul_comm] using hh
  have hS : 1 ≤ S := by
    have hh := sinhc_taylor_lower hx
    dsimp only [S]
    nlinarith [sq_nonneg x, pow_nonneg hx.le 4, pow_nonneg hx.le 6]
  have hL : D ^ 2 - B ^ 2 ≤ L := by
    have hh := logarithmic_covariance hab
    dsimp only [D, B, L]
    apply (le_div_iff₀ hδ).mpr
    field_simp [ne_of_gt hδ]
    dsimp only [δ]
    nlinarith
  have hC : R * L ≤ arithmeticMean a b := arithmeticMean_ge_hyperbolic h hab
  have hR : 1 + growthStep a * (1 - 1 / S) ≤ R := by
    have hh := sinhc_comparison hx (growthStep_nonneg a) (growthStep_le_one a)
    have hi : 1 / S = (x / Real.sinh x) ^ 2 := by
      dsimp only [S, sinhc]
      rw [if_neg (ne_of_gt hx)]
      field_simp [ne_of_gt hx, ne_of_gt (Real.sinh_pos_iff.mpr hx)]
    simpa only [hi] using hh
  have hh := algebraic_average_surplus hD hB hBD hS (growthStep_nonneg a) hL hC hR
  have hs : surplus a b ≤ (3 / 4 : ℝ) * (1 + growthStep a) * (S - 1) := by
    have hh := sinhc_surplus hx (growthStep_nonneg a)
    have hsep : separation a b = -(2 * x) := by dsimp [separation, x, δ]; ring
    simpa only [surplus, min_eq_left hab.le, hsep, neg_sq,
      show (-(2 * x)) ^ 4 = (2 * x) ^ 4 by ring] using hh
  have hratio : dividedDifference transportRatio a b = B / D := by
    simp only [dividedDifference, if_neg (ne_of_lt hab)]
    dsimp only [B, D]
    field_simp [ne_of_gt hδ, ne_of_gt (sub_pos.mpr hab), sub_ne_zero.mpr (ne_of_lt hab)]
    <;> ring
  have hscale : dividedDifference gaussianHazard a b ^ 2 /
      (gaussianHazard a * gaussianHazard b) = S / D ^ 2 := by
    have hh := log_secant_scale (gaussianHazard_pos a) (gaussianHazard_pos b) (ne_of_gt hδ)
    simp only [dividedDifference, if_neg (ne_of_lt hab)]
    dsimp only [S, D, x, sinhc]
    rw [if_neg (ne_of_gt hx)]
    dsimp only [x] at hx
    dsimp only [δ] at *
    field_simp [ne_of_gt (gaussianHazard_pos a), ne_of_gt (gaussianHazard_pos b),
      ne_of_gt hδ, sub_ne_zero.mpr (ne_of_lt hab), ne_of_gt (sub_pos.mpr hab)] at hh ⊢
    nlinarith
  rw [hratio]
  calc
    _ ≤ 1 - (B / D) ^ 2 + (3 / 4 : ℝ) * (1 + growthStep a) * (S - 1) := add_le_add_right hs _
    _ ≤ S * arithmeticMean a b / D ^ 2 := hh
    _ = S / D ^ 2 * arithmeticMean a b := by ring
    _ = _ := by rw [← hscale]; ring

lemma secant_surplus (h : GrowthCertificate) (a b : ℝ) :
    1 - dividedDifference transportRatio a b ^ 2 + surplus a b ≤
      dividedDifference gaussianHazard a b ^ 2 * arithmeticMean a b /
        (gaussianHazard a * gaussianHazard b) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact secant_surplus_of_lt h hab
  · subst b
    exact (diagonal_identity a).le
  · simpa only [dividedDifference_symm _ b a, surplus_symm b a,
      arithmeticMean_symm b a, mul_comm (gaussianHazard b) (gaussianHazard a)] using
      secant_surplus_of_lt h hab

lemma hazard_secant_surplus_of_certificate (h : GrowthCertificate) (a b : ℝ) :
    arithmeticMean a b = arithmeticMean b a ∧
      (a ≤ b → ∀ c, arithmeticMean a c ≤ arithmeticMean b c) ∧
      1 - dividedDifference transportRatio a b ^ 2 + surplus a b ≤
        dividedDifference gaussianHazard a b ^ 2 * arithmeticMean a b /
          (gaussianHazard a * gaussianHazard b) := by
  exact ⟨arithmeticMean_symm a b,
    fun hab c => monotone_arithmeticMean_of_monotone (monotone_scalarM h) c hab,
    secant_surplus h a b⟩

end Submission.Obl.Entropy__hazard_secant_surplus
