/-
Adapted from: here:root
Original scalar logarithmic estimates by session x0023, following Section 4 of the supplied paper.
-/

import Mathlib

/-! Elementary logarithmic estimates used in the scalar absorption argument (Section 4). -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set

namespace Submission.Lib.ScalarLog

noncomputable def kernel (s x : ℝ) : ℝ := s * x / (1 - x + s * x)

/-- The integral formula includes the continuous value `1/2` at `s = 1`. -/
noncomputable def logCost (s : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, kernel s x

lemma denom_pos {s x : ℝ} (hs : 0 < s) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < 1 - x + s * x := by
  have hm := mul_nonneg hs.le hx.1
  by_cases h : x < 1
  · linarith
  · have he : x = 1 := le_antisymm hx.2 (not_lt.mp h)
    simpa [he] using hs

lemma kernel_intervalIntegrable {s : ℝ} (hs : 0 < s) :
    IntervalIntegrable (kernel s) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  exact (denom_pos hs hx).ne'

lemma logCost_one : logCost 1 = 1 / 2 := by
  simp [logCost, kernel, integral_id]

lemma logCost_eq {s : ℝ} (hs : 0 < s) (hs1 : s ≠ 1) :
    logCost s = s * (s - 1 - Real.log s) / (1 - s) ^ 2 := by
  have hc : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  let F := fun x : ℝ => s / (s - 1) ^ 2 * ((s - 1) * x - Real.log (1 - x + s * x))
  have hd (x : ℝ) (hx : x ∈ uIcc (0 : ℝ) 1) : HasDerivAt F (kernel s x) x := by
    have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
    have hp := denom_pos hs hx'
    have hden : HasDerivAt (fun y : ℝ => 1 - y + s * y) (-1 + s) x := by
      convert ((hasDerivAt_id x).const_sub 1).add ((hasDerivAt_id x).const_mul s) using 1 <;>
        first | rfl | norm_num
    convert (((hasDerivAt_id x).const_mul (s - 1)).sub (hden.log hp.ne')).const_mul
      (s / (s - 1) ^ 2) using 1
    all_goals try rfl
    dsimp [kernel]
    field_simp
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (kernel_intervalIntegrable hs)
  change logCost s = _ at hint
  rw [hint]
  dsimp [F]
  norm_num
  field_simp
  ring

/-- The rational logarithm enclosure needed for the tangent coefficients. -/
lemma log_seven_twentyfive_bounds :
    -(1275 / 1000 : ℝ) ≤ Real.log (7 / 25) ∧ Real.log (7 / 25) ≤ -(127 / 100 : ℝ) := by
  have hlo := Real.sum_range_le_log_div (x := (9 / 16 : ℝ)) (by norm_num) (by norm_num) 6
  have hhi := Real.log_div_le_sum_range_add (x := (9 / 16 : ℝ)) (by norm_num) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hlo hhi
  have hlog : Real.log (7 / 25 : ℝ) = -Real.log (25 / 7 : ℝ) := by
    rw [show (7 / 25 : ℝ) = (25 / 7 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hlog]
  constructor <;> linarith

/-- Pointwise supporting line for the integral kernel at `a = 7/25`. -/
lemma kernel_le_tangent {s x : ℝ} (hs : 0 < s) (hx : x ∈ Icc (0 : ℝ) 1) :
    kernel s x ≤ ((7 / 25 * x) ^ 2 + s * x * (1 - x)) /
      (1 - x + 7 / 25 * x) ^ 2 := by
  have hd := denom_pos hs hx
  have ha := denom_pos (by norm_num : (0 : ℝ) < 7 / 25) hx
  rw [kernel, div_le_div_iff₀ hd (sq_pos_of_pos ha)]
  have hnonneg := mul_nonneg (mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx.2))
    (sq_nonneg (s - 7 / 25))
  nlinarith only [hnonneg]

/-- Exact integral of the rational supporting line. -/
lemma integral_tangent (s : ℝ) :
    (∫ x in (0 : ℝ)..1, ((7 / 25 * x) ^ 2 + s * x * (1 - x)) /
      (1 - x + 7 / 25 * x) ^ 2) =
      (56 / 81 + 1225 / 2916 * Real.log (7 / 25)) +
        s * (-(625 / 162) - 2500 / 729 * Real.log (7 / 25)) := by
  let D := fun x : ℝ => 1 - x + 7 / 25 * x
  let G := fun x : ℝ =>
    -(1225 / 5832) * (D x - 2 * Real.log (D x) - 1 / D x) -
      s * (15625 / 5832) * (-D x + 32 / 25 * Real.log (D x) + (7 / 25) / D x)
  have hD (x : ℝ) : HasDerivAt D (-(18 / 25)) x := by
    dsimp [D]
    convert ((hasDerivAt_id x).const_sub 1).add ((hasDerivAt_id x).const_mul (7 / 25)) using 1 <;>
      first | rfl | norm_num
  have hd (x : ℝ) (hx : x ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt G (((7 / 25 * x) ^ 2 + s * x * (1 - x)) / D x ^ 2) x := by
    have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
    have hn : D x ≠ 0 := (denom_pos (by norm_num : (0 : ℝ) < 7 / 25) hx').ne'
    have hlog := (hD x).log hn
    have hinv := (hD x).inv hn
    convert (((hD x).sub (hlog.const_mul 2)).sub hinv).const_mul (-(1225 / 5832)) |>.sub
      ((((hD x).neg.add (hlog.const_mul (32 / 25))).add
        (hinv.const_mul (7 / 25))).const_mul (s * (15625 / 5832))) using 1
    all_goals try rfl
    · ext y
      simp [G, div_eq_mul_inv]
    · field_simp [hn]
      dsimp [D]
      ring
  have hint : IntervalIntegrable (fun x : ℝ =>
      ((7 / 25 * x) ^ 2 + s * x * (1 - x)) / D x ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply ContinuousOn.div (by fun_prop) (by dsimp [D]; fun_prop)
    intro x hx
    exact pow_ne_zero 2 (denom_pos (by norm_num : (0 : ℝ) < 7 / 25) hx).ne'
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  change (∫ x in (0 : ℝ)..1, ((7 / 25 * x) ^ 2 + s * x * (1 - x)) / D x ^ 2) = _
  rw [heq]
  dsimp [G, D]
  norm_num
  ring

/-- The tangent bound in the paper's logarithmic absorption estimate. -/
theorem logCost_le_affine {s : ℝ} (hs : 0 < s) : logCost s ≤ 4 / 25 + 13 / 25 * s := by
  have hi : IntervalIntegrable (fun x : ℝ =>
      ((7 / 25 * x) ^ 2 + s * x * (1 - x)) / (1 - x + 7 / 25 * x) ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    exact pow_ne_zero 2 (denom_pos (by norm_num : (0 : ℝ) < 7 / 25) hx).ne'
  have hb := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (kernel_intervalIntegrable hs) hi (fun x hx => kernel_le_tangent hs hx)
  rw [integral_tangent] at hb
  obtain ⟨hlo, hhi⟩ := log_seven_twentyfive_bounds
  have hA : 56 / 81 + 1225 / 2916 * Real.log (7 / 25 : ℝ) ≤ (4 / 25 : ℝ) := by linarith
  have hB : -(625 / 162) - 2500 / 729 * Real.log (7 / 25 : ℝ) ≤ (13 / 25 : ℝ) := by linarith
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left hB hs.le])

/-- The uniform part of equation (4.8), with the paper's exact rational constants. -/
theorem logCost_rho_le {s : ℝ} (hs : 0 < s) :
    (3 / 40) * logCost s / (3 / 20 + 1813 / 4000 * s) ≤ (89 / 1000 : ℝ) := by
  have hrho : 0 < (3 / 20 : ℝ) + 1813 / 4000 * s := by positivity
  apply (div_le_iff₀ hrho).mpr
  have h := logCost_le_affine hs
  nlinarith

end Submission.Lib.ScalarLog
