/-
Adapted from: here:root
Original Section 4 logarithmic estimates by sessions x0014.
-/

import Mathlib

open Set

set_option backward.isDefEq.respectTransparency false

namespace Submission.Lib.ScalarLog

/-- A rational lower bound for the logarithm on `(0,1]`, obtained by bounding the
remainder of its odd-power expansion. Its derivative is verified algebraically. -/
noncomputable def logMinorant (x : ℝ) : ℝ :=
  2 * ((x - 1) / (x + 1)) + (2 / 3 : ℝ) * ((x - 1) / (x + 1)) ^ 3 +
    (x - 1) ^ 5 / (10 * x * (x + 1) ^ 3)

theorem hasDerivAt_log_sub_minorant {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t => Real.log t - logMinorant t)
      (-(x - 1) ^ 6 / (10 * x ^ 2 * (x + 1) ^ 4)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hx1 : x + 1 ≠ 0 := by positivity
  have hz := ((hasDerivAt_id x).sub_const 1).div
    ((hasDerivAt_id x).add_const 1) hx1
  have hn := ((hasDerivAt_id x).sub_const 1).pow 5
  have hd := ((hasDerivAt_id x).const_mul 10).mul
    (((hasDerivAt_id x).add_const 1).pow 3)
  have hr := ((hz.const_mul 2).add ((hz.pow 3).const_mul (2 / 3))).add
    (hn.div hd (by dsimp; positivity))
  have hG := (Real.hasDerivAt_log hx0).sub hr
  change HasDerivAt (fun t => Real.log t - logMinorant t) _ x at hG
  apply hG.congr_deriv
  dsimp
  field_simp
  ring

theorem logMinorant_le_log {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    logMinorant x ≤ Real.log x := by
  have hanti : AntitoneOn (fun t => Real.log t - logMinorant t) (Ioi 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
    · intro t ht
      exact (hasDerivAt_log_sub_minorant ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hasDerivAt_log_sub_minorant (by simpa using ht)).hasDerivWithinAt
    · intro t ht
      have ht0 : 0 < t := by simpa using ht
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)
  have h := hanti hx (by norm_num) hx1
  norm_num [logMinorant] at h
  simpa only [logMinorant] using h

/-- The polynomial left after substituting the rational logarithm bound. -/
noncomputable def certificatePoly (x : ℝ) : ℝ :=
  417 - 2015 * x - 130 * x ^ 2 + 10470 * x ^ 3 + 23085 * x ^ 4 +
    21717 * x ^ 5 + 10500 * x ^ 6 + 2100 * x ^ 7

theorem certificatePoly_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ certificatePoly x := by
  by_cases hxq : x ≤ 1 / 4
  · have ha : 0 ≤ 4 * x := by positivity
    have hb : 0 ≤ 1 - 4 * x := by linarith
    have h : certificatePoly x =
        417 * (1 - 4 * x) ^ 7 + (9661 / 4 : ℝ) * (4 * x) * (1 - 4 * x) ^ 6 +
        (45811 / 8 : ℝ) * (4 * x) ^ 2 * (1 - 4 * x) ^ 5 +
        (229175 / 32 : ℝ) * (4 * x) ^ 3 * (1 - 4 * x) ^ 4 +
        (1326925 / 256 : ℝ) * (4 * x) ^ 4 * (1 - 4 * x) ^ 3 +
        (2450225 / 1024 : ℝ) * (4 * x) ^ 5 * (1 - 4 * x) ^ 2 +
        (845575 / 1024 : ℝ) * (4 * x) ^ 6 * (1 - 4 * x) +
        (748725 / 4096 : ℝ) * (4 * x) ^ 7 := by
      unfold certificatePoly
      ring
    rw [h]
    positivity
  · have ha : 0 ≤ x - 1 / 4 := by linarith
    have h : certificatePoly x =
        (748725 / 4096 : ℝ) + (1858775 / 1024 : ℝ) * (x - 1 / 4) +
        (5230325 / 256 : ℝ) * (x - 1 / 4) ^ 2 +
        (3244575 / 64 : ℝ) * (x - 1 / 4) ^ 3 +
        (979575 / 16 : ℝ) * (x - 1 / 4) ^ 4 +
        (160893 / 4 : ℝ) * (x - 1 / 4) ^ 5 +
        14175 * (x - 1 / 4) ^ 6 + 2100 * (x - 1 / 4) ^ 7 := by
      unfold certificatePoly
      ring
    rw [h]
    positivity

/-- The logarithmic estimate before substituting `x = sqrt S`. -/
theorem log_sqrt_aux {x : ℝ} (hx : 0 < x) :
    x * (x ^ 2 - 1 - 2 * Real.log x) ≤
      ((239 / 500 : ℝ) + (7 / 5 : ℝ) * x ^ 2) * (1 - x ^ 2) ^ 2 := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  by_cases hx1 : x ≤ 1
  · have hlog := logMinorant_le_log hx hx1
    have hQ := certificatePoly_nonneg hx.le
    have heq :
        ((239 / 500 : ℝ) + (7 / 5 : ℝ) * x ^ 2) * (1 - x ^ 2) ^ 2 -
          x * (x ^ 2 - 1 - 2 * logMinorant x) =
        (x - 1) ^ 2 * certificatePoly x / (1500 * (x + 1) ^ 3) := by
      unfold logMinorant certificatePoly
      field_simp
      ring
    have hcert : 0 ≤
        ((239 / 500 : ℝ) + (7 / 5 : ℝ) * x ^ 2) * (1 - x ^ 2) ^ 2 -
          x * (x ^ 2 - 1 - 2 * logMinorant x) := by
      rw [heq]
      positivity
    calc
      _ ≤ x * (x ^ 2 - 1 - 2 * logMinorant x) :=
        mul_le_mul_of_nonneg_left (by linarith) hx.le
      _ ≤ _ := sub_nonneg.mp hcert
  · have hx1' : 0 ≤ x - 1 := by linarith
    have hlog := Real.one_sub_inv_le_log_of_pos hx
    have heq :
        ((239 / 500 : ℝ) + (7 / 5 : ℝ) * x ^ 2) * (1 - x ^ 2) ^ 2 -
          x * (x ^ 2 - 1 - 2 * (1 - x⁻¹)) =
        (564 / 125 : ℝ) * (x - 1) ^ 2 + (2214 / 125 : ℝ) * (x - 1) ^ 3 +
          (9339 / 500 : ℝ) * (x - 1) ^ 4 + (42 / 5 : ℝ) * (x - 1) ^ 5 +
          (7 / 5 : ℝ) * (x - 1) ^ 6 := by
      field_simp
      ring
    have hcert : 0 ≤
        ((239 / 500 : ℝ) + (7 / 5 : ℝ) * x ^ 2) * (1 - x ^ 2) ^ 2 -
          x * (x ^ 2 - 1 - 2 * (1 - x⁻¹)) := by
      rw [heq]
      positivity
    calc
      _ ≤ x * (x ^ 2 - 1 - 2 * (1 - x⁻¹)) :=
        mul_le_mul_of_nonneg_left (by linarith) hx.le
      _ ≤ _ := sub_nonneg.mp hcert

/-- The square-root logarithmic estimate of Section 4, with denominators cleared. -/
theorem scalar_log_sqrt_bound {S : ℝ} (hS : 0 < S) :
    S * (S - 1 - Real.log S) ≤
      ((239 / 500 : ℝ) + (7 / 5 : ℝ) * S) * Real.sqrt S * (1 - S) ^ 2 := by
  have h := log_sqrt_aux (Real.sqrt_pos.mpr hS)
  rw [Real.sq_sqrt hS.le, Real.log_sqrt hS.le] at h
  have h' := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg S)
  rw [← mul_assoc, Real.mul_self_sqrt hS.le] at h'
  calc
    _ = S * (S - 1 - 2 * (Real.log S / 2)) := by ring
    _ ≤ Real.sqrt S * (((239 / 500 : ℝ) + (7 / 5 : ℝ) * S) * (1 - S) ^ 2) := h'
    _ = _ := by ring

/-- `F₀(S)/sqrt S ≤ .478 + 1.4 S`, including the continuous value at one. -/
theorem scalar_log_sqrt_ratio_bound {S : ℝ} (hS : 0 < S) :
    (if S = 1 then (1 / 2 : ℝ) else S * (S - 1 - Real.log S) / (1 - S) ^ 2) /
        Real.sqrt S ≤ (239 / 500 : ℝ) + (7 / 5 : ℝ) * S := by
  by_cases hS1 : S = 1
  · subst S
    norm_num
  · rw [if_neg hS1, div_le_iff₀ (Real.sqrt_pos.mpr hS),
      div_le_iff₀ (sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm hS1)))]
    exact scalar_log_sqrt_bound hS

/-- The square-root part of the absorption estimate, written without division by
`sqrt lam` so it also covers `lam = 0`. -/
theorem scalar_log_sqrt_absorption {S lam : ℝ} (hS : 0 < S) (hlam : 0 ≤ lam)
    (hprod : S * lam ≤ 40 / 3) :
    (3 / 40 : ℝ) *
        (if S = 1 then (1 / 2 : ℝ) else S * (S - 1 - Real.log S) / (1 - S) ^ 2) *
        Real.sqrt lam ≤
      (22 / 25 : ℝ) * ((3 / 20 : ℝ) + (1813 / 4000 : ℝ) * S) := by
  have hF := (div_le_iff₀ (Real.sqrt_pos.mpr hS)).mp (scalar_log_sqrt_ratio_bound hS)
  have hr : Real.sqrt S * Real.sqrt lam ≤ 11 / 3 := by
    have heq : (Real.sqrt S * Real.sqrt lam) ^ 2 = S * lam := by
      rw [mul_pow, Real.sq_sqrt hS.le, Real.sq_sqrt hlam]
    nlinarith [mul_nonneg (Real.sqrt_nonneg S) (Real.sqrt_nonneg lam)]
  have ha : 0 ≤ (239 / 500 : ℝ) + (7 / 5 : ℝ) * S := by positivity
  calc
    _ ≤ (3 / 40 : ℝ) *
        (((239 / 500 : ℝ) + (7 / 5 : ℝ) * S) * Real.sqrt S) * Real.sqrt lam :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF (by norm_num))
        (Real.sqrt_nonneg lam)
    _ = ((3 / 40 : ℝ) * ((239 / 500 : ℝ) + (7 / 5 : ℝ) * S)) *
        (Real.sqrt S * Real.sqrt lam) := by ring
    _ ≤ ((3 / 40 : ℝ) * ((239 / 500 : ℝ) + (7 / 5 : ℝ) * S)) * (11 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ ≤ _ := by linarith

end Submission.Lib.ScalarLog
