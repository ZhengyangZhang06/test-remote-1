import Mathlib

/-!
The hyperbolic estimates in the proof of Proposition 2.5 of the supplied
paper. All constants are exact rationals, including the degree-six surplus.
-/

namespace Submission.Obl.Entropy__transport_energy_surplus

open scoped BigOperators

/-- The continuous value of `sinh x / x` at zero. -/
noncomputable def shc (x : ℝ) : ℝ := if x = 0 then 1 else Real.sinh x / x

/-- The continuous value of `x coth x - 1` at zero. -/
noncomputable def cothDefect (x : ℝ) : ℝ :=
  if x = 0 then 0 else x * Real.cosh x / Real.sinh x - 1

theorem cosh_taylor_lower (x : ℝ) :
    1 + x ^ 2 / 2 + x ^ 4 / 24 + x ^ 6 / 720 + x ^ 8 / 40320 ≤ Real.cosh x := by
  have h := (Real.hasSum_cosh x).summable.sum_le_tsum (Finset.range 5)
    (fun n _ => div_nonneg (by rw [pow_mul]; positivity) (Nat.cast_nonneg _))
  rw [(Real.hasSum_cosh x).tsum_eq] at h
  norm_num [Finset.sum_range_succ] at h
  exact h

theorem sinh_sq_taylor_lower (x : ℝ) :
    x ^ 2 + x ^ 4 / 3 + 2 * x ^ 6 / 45 + x ^ 8 / 315 ≤ Real.sinh x ^ 2 := by
  have h := cosh_taylor_lower (2 * x)
  rw [Real.cosh_two_mul] at h
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

theorem shc_sq_taylor_lower (x : ℝ) :
    1 + x ^ 2 / 3 + 2 * x ^ 4 / 45 + x ^ 6 / 315 ≤ shc x ^ 2 := by
  by_cases hx : x = 0
  · simp [shc, hx]
  · rw [shc, if_neg hx, div_pow, le_div_iff₀ (sq_pos_of_ne_zero hx)]
    nlinarith [sinh_sq_taylor_lower x]

/-- The last scalar inequality in Proposition 2.5, in its original normalization. -/
theorem hyperbolic_surplus_lower (m δ : ℝ) (hm : 0 ≤ m) :
    (1 + m) / 16 * (δ ^ 2 + δ ^ 4 / 30 + δ ^ 6 / 1680) ≤
      (3 / 4 : ℝ) * (1 + m) * (shc (δ / 2) ^ 2 - 1) := by
  have h := shc_sq_taylor_lower (δ / 2)
  have hmul := mul_nonneg (show 0 ≤ (3 / 4 : ℝ) * (1 + m) by positivity)
    (sub_nonneg.mpr h)
  nlinarith

/-- Comparison of the positive tails of `cosh (2x)` and `(x/2) sinh (2x)`. -/
private theorem hyperbolic_tail_term (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (2 * x) ^ (2 * (n + 2)) / ((2 * (n + 2)).factorial : ℝ) ≤
      x / 2 * ((2 * x) ^ (2 * (n + 1) + 1) /
        ((2 * (n + 1) + 1).factorial : ℝ)) := by
  have hf : (0 : ℝ) < ((2 * (n + 1) + 1).factorial : ℝ) := by positivity
  have he : 2 * (n + 2) = (2 * (n + 1) + 1) + 1 := by omega
  rw [he, Nat.factorial_succ, pow_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) <
    (↑(2 * (n + 1) + 1) + 1) * ↑(2 * (n + 1) + 1).factorial)]
  field_simp
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : 0 ≤ (2 * x) ^ (2 * (n + 1) + 1) := pow_nonneg (by positivity) _
  push_cast
  nlinarith [mul_nonneg (mul_nonneg hn hx) hp]

/-- The hyperbolic inequality used twice in the paper's average comparison. -/
theorem hyperbolic_core (x : ℝ) (hx : 0 ≤ x) :
    2 * Real.sinh x ^ 2 ≤ x * Real.sinh x * Real.cosh x + x ^ 2 := by
  have hc := (hasSum_nat_add_iff' 2).mpr (Real.hasSum_cosh (2 * x))
  have hs := ((hasSum_nat_add_iff' 1).mpr (Real.hasSum_sinh (2 * x))).mul_left (x / 2)
  have h := hc.summable.tsum_le_tsum (hyperbolic_tail_term x hx) hs.summable
  rw [hc.tsum_eq, hs.tsum_eq] at h
  norm_num [Finset.sum_range_succ] at h
  rw [Real.cosh_two_mul, Real.sinh_two_mul] at h
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

private theorem hasDerivAt_normalized_cothDefect (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y * Real.cosh y / Real.sinh y - 1) / y ^ 2)
      ((2 * Real.sinh x ^ 2 - x ^ 2 - x * Real.sinh x * Real.cosh x) /
        (x ^ 3 * Real.sinh x ^ 2)) x := by
  have hs : Real.sinh x ≠ 0 := (Real.sinh_pos_iff.mpr hx).ne'
  have hd := (((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).div
    (Real.hasDerivAt_sinh x) hs).sub_const 1
  convert! hd.div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx.ne') using 1
  dsimp
  field_simp
  rw [Real.cosh_sq]
  ring

/-- `A₀(x) / x²` decreases on the positive half-line. -/
theorem normalized_cothDefect_antitone :
    AntitoneOn (fun x : ℝ => (x * Real.cosh x / Real.sinh x - 1) / x ^ 2)
      (Set.Ioi 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
  · apply continuousOn_of_forall_continuousAt
    intro x hx
    exact (hasDerivAt_normalized_cothDefect x hx).continuousAt
  · intro x hx
    exact (hasDerivAt_normalized_cothDefect x (by simpa using hx)).hasDerivWithinAt
  · intro x hx
    have hx0 : 0 < x := by simpa using hx
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith [hyperbolic_core x hx0.le]
    · positivity

theorem cothDefect_scale (m x : ℝ) (hm : 0 ≤ m) (hm1 : m ≤ 1) (hx : 0 ≤ x) :
    m ^ 2 * cothDefect x ≤ cothDefect (m * x) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [cothDefect]
  rcases hm.eq_or_lt with rfl | hm
  · simp [cothDefect]
  have h := normalized_cothDefect_antitone (mul_pos hm hx) hx
    (mul_le_of_le_one_left hx.le hm1)
  rw [div_le_div_iff₀ (sq_pos_of_pos hx) (sq_pos_of_pos (mul_pos hm hx))] at h
  simp only [cothDefect, if_neg hx.ne', if_neg (mul_pos hm hx).ne']
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hx)).mp
  nlinarith only [h]

theorem cothDefect_lower (x : ℝ) (hx : 0 < x) :
    1 - (x / Real.sinh x) ^ 2 ≤ cothDefect x := by
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  rw [cothDefect, if_neg hx.ne']
  have h := hyperbolic_core x hx.le
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hs)).mp
  field_simp
  nlinarith

theorem shc_pos (x : ℝ) : 0 < shc x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp only [shc, if_neg hx.ne]
    exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr hx) hx
  · norm_num [shc]
  · simp only [shc, if_neg hx.ne']
    exact div_pos (Real.sinh_pos_iff.mpr hx) hx

private theorem hyperbolic_ratio_identity (m x : ℝ) (hm : 0 < m) (hx : 0 < x) :
    shc ((1 + m) * x) / (shc x * shc (m * x)) =
      1 + (m * cothDefect x + cothDefect (m * x)) / (1 + m) := by
  have hmx := mul_pos hm hx
  have hsum : 0 < 1 + m := by linarith
  have hsx : Real.sinh x ≠ 0 := (Real.sinh_pos_iff.mpr hx).ne'
  have hsmx : Real.sinh (m * x) ≠ 0 := (Real.sinh_pos_iff.mpr hmx).ne'
  simp only [shc, cothDefect, if_neg hx.ne', if_neg hmx.ne',
    if_neg (mul_pos hsum hx).ne']
  rw [show (1 + m) * x = x + m * x by ring, Real.sinh_add]
  field_simp
  ring

/-- The explicit comparison between arithmetic and logarithmic averaging factors. -/
theorem hyperbolic_average_comparison (m x : ℝ)
    (hm : 0 ≤ m) (hm1 : m ≤ 1) (hx : 0 ≤ x) :
    1 + m * (1 - (shc x)⁻¹ ^ 2) ≤
      shc ((1 + m) * x) / (shc x * shc (m * x)) := by
  rcases hx.eq_or_lt with rfl | hx
  · norm_num [shc]
  rcases hm.eq_or_lt with rfl | hm
  · have hz : shc 0 = 1 := by simp [shc]
    simp [hz, ne_of_gt (shc_pos x)]
  rw [hyperbolic_ratio_identity m x hm hx]
  have he : (shc x)⁻¹ = x / Real.sinh x := by simp [shc, hx.ne']
  rw [he, add_le_add_iff_left, le_div_iff₀ (by linarith : 0 < 1 + m)]
  have hs := cothDefect_scale m x hm.le hm1 hx.le
  have hl := mul_le_mul_of_nonneg_left (cothDefect_lower x hx)
    (show 0 ≤ m * (1 + m) by positivity)
  nlinarith

end Submission.Obl.Entropy__transport_energy_surplus
