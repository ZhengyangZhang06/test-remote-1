/-
Adapted from: here:o006

Original proofs by session x0016, developed for the supplied paper.
-/

import Mathlib
import Submission.Lib.EntropyTools.Remainder

/-!
# Summing the final Gaussian-chaos inequality

This proves the numerical summation at the end of Theorem 3.1. The
analytic chaos decomposition is a separate input: `a d` denotes the
squared norm of the degree-`d` component of the nonlinear field.
-/

namespace Submission.Lib.EntropyRemainder

open Submission.Lib.EntropyTools
open scoped BigOperators

/-- Positivity of the quadratic form in Proposition 3.6. -/
theorem chaosQuadratic_nonneg (u v : ℝ) : 0 ≤ chaosQuadratic u v := by
  have h : chaosQuadratic u v =
      (43 / 100 : ℝ) * (u + (13 / 43) * v) ^ 2 + (11527 / 4300 : ℝ) * v ^ 2 := by
    unfold chaosQuadratic
    ring
  rw [h]
  positivity

/-- The cost coefficient after using `g = G/d` and `‖G‖² = d ‖Y‖²`. -/
noncomputable def chaosCost (d : ℕ) : ℝ :=
  chaosQuadratic 1 ((d : ℝ)⁻¹ - 1 / 2) * (d : ℝ)

theorem chaosCost_nonneg (d : ℕ) : 0 ≤ chaosCost d :=
  mul_nonneg (chaosQuadratic_nonneg _ _) (Nat.cast_nonneg _)

/-- Every degree at least two pays for `57/50` times its squared field norm. -/
theorem chaosCost_le {d : ℕ} (hd : 2 ≤ d) : chaosCost d ≤ (d : ℝ) - 57 / 50 := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hhalf : (d : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hd')
  have h := mul_le_mul_of_nonneg_right
    (chaos_quadratic_bound (inv_nonneg.mpr hdpos.le) hhalf) hdpos.le
  rw [add_mul, sub_mul, one_mul, mul_assoc, inv_mul_cancel₀ hdpos.ne'] at h
  dsimp [chaosCost]
  linarith

/-- Finite derivative energy controls the sum of the higher-chaos field norms. -/
theorem summable_chaos_mass {a : ℕ → ℝ} (ha : ∀ d, 0 ≤ a d) (ha0 : a 0 = 0)
    (henergy : Summable (fun d : ℕ => (d : ℝ) * a d)) : Summable a := by
  apply Summable.of_nonneg_of_le ha _ henergy
  intro d
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [ha0]
  · have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    simpa using mul_le_mul_of_nonneg_right hd' (ha d)

/-- The summed quadratic cost is defined by an absolutely convergent series. -/
theorem summable_chaos_cost {a : ℕ → ℝ} (ha : ∀ d, 0 ≤ a d)
    (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (henergy : Summable (fun d : ℕ => (d : ℝ) * a d)) :
    Summable (fun d => chaosCost d * a d) := by
  refine Summable.of_nonneg_of_le (fun d => mul_nonneg (chaosCost_nonneg d) (ha d)) ?_ henergy
  intro d
  rcases Nat.lt_or_ge d 2 with hd | hd
  · interval_cases d <;> simp [ha0, ha1]
  · apply mul_le_mul_of_nonneg_right _ (ha d)
    exact (chaosCost_le hd).trans (by linarith)

/-- The final polynomial inequality summed over all higher Gaussian chaoses. -/
theorem chaos_summed_bound {a : ℕ → ℝ} (ha : ∀ d, 0 ≤ a d)
    (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (henergy : Summable (fun d : ℕ => (d : ℝ) * a d)) :
    (∑' d, chaosCost d * a d) ≤
      (∑' d : ℕ, (d : ℝ) * a d) - (57 / 50) * ∑' d, a d := by
  have hmass := summable_chaos_mass ha ha0 henergy
  have hcost := summable_chaos_cost ha ha0 ha1 henergy
  have hright := henergy.sub (hmass.mul_left (57 / 50 : ℝ))
  have hle (d : ℕ) : chaosCost d * a d ≤ (d : ℝ) * a d - (57 / 50) * a d := by
    rcases Nat.lt_or_ge d 2 with hd | hd
    · interval_cases d <;> simp [ha0, ha1]
    · simpa only [sub_mul] using mul_le_mul_of_nonneg_right (chaosCost_le hd) (ha d)
  have h := Summable.tsum_le_tsum hle hcost hright
  rw [henergy.tsum_sub (hmass.mul_left (57 / 50 : ℝ)), tsum_mul_left] at h
  exact h

/-- Cancellation of the separation surplus leaves the strict remainder. -/
theorem strict_remainder_of_chaos_bound
    {deficit surplus field derivative pair omega : ℝ}
    (hpre : deficit ≤ -(derivative - field) - surplus +
      (69 / 500) * field - omega / 1000 + pair)
    (hpair : pair ≤ derivative - (57 / 50) * field + surplus) :
    field / 500 + omega / 1000 ≤ -deficit := by
  linarith

end Submission.Lib.EntropyRemainder
