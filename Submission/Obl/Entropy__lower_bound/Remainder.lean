import Mathlib

/-!
# Scalar closing steps in the smooth entropy argument

The weight is equation (3.1) of the paper, including its specified value at
zero. The polynomial identity is the last step in the proof of Theorem 3.1.
-/

open scoped BigOperators

namespace Submission.Obl.Entropy__lower_bound

/-- The cutoff in the rigidity weight, with the paper's convention at zero. -/
noncomputable def rigidityCutoff (a : ℝ) : ℝ :=
  if a = 0 then 13 / 100 else min (13 / 100) (32 / (25 * Real.sqrt a))

/-- The weight retained by the strict remainder estimate. -/
noncomputable def rigidityWeight (a : ℝ) : ℝ :=
  (3 * (a - 1) ^ 2 / (37 + 3 * a)) *
    (3 / 20 + (49 / 100) * (37 / (37 + 3 * a))) * rigidityCutoff a

/-- In particular, the convention at zero keeps this factor strictly positive. -/
theorem rigidityCutoff_pos {a : ℝ} (ha : 0 ≤ a) : 0 < rigidityCutoff a := by
  unfold rigidityCutoff
  split_ifs with h
  · norm_num
  · exact lt_min (by norm_num) (div_pos (by norm_num)
      (mul_pos (by norm_num) (Real.sqrt_pos.2 (lt_of_le_of_ne ha (Ne.symm h)))))

/-- The strict remainder never decreases the basic entropy lower bound. -/
theorem rigidityWeight_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ rigidityWeight a := by
  unfold rigidityWeight
  exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (rigidityCutoff_pos ha).le

/-- The only zero of the rigidity weight on its intended domain is one. -/
theorem rigidityWeight_eq_zero_iff {a : ℝ} (ha : 0 ≤ a) :
    rigidityWeight a = 0 ↔ a = 1 := by
  have hd : 0 < 37 + 3 * a := by positivity
  have hp : 0 < (3 : ℝ) / 20 + (49 / 100) * (37 / (37 + 3 * a)) := by positivity
  simp only [rigidityWeight, mul_eq_zero, div_eq_zero_iff, sq_eq_zero_iff,
    (ne_of_gt hd), (ne_of_gt hp), (ne_of_gt (rigidityCutoff_pos ha)),
    sub_eq_zero, or_false]
  norm_num

/-- The quadratic form in Proposition 3.6. -/
noncomputable def chaosQuadratic (u v : ℝ) : ℝ :=
  (43 / 100) * u ^ 2 + (26 / 100) * u * v + (68 / 25) * v ^ 2

/-- The paper's exact rational factorization; no numerical approximation is used. -/
theorem chaos_polynomial_identity (r : ℝ) :
    1 - r - chaosQuadratic 1 (r - 1 / 2) - (7 / 50) * r =
      (1 - 2 * r) * (1 + 68 * r) / 50 := by
  unfold chaosQuadratic
  ring

/-- The final scalar estimate for every Gaussian chaos degree at least two. -/
theorem chaos_quadratic_bound {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) :
    chaosQuadratic 1 (r - 1 / 2) + (7 / 50) * r ≤ 1 - r := by
  have h : 0 ≤ (1 - 2 * r) * (1 + 68 * r) / 50 :=
    div_nonneg (mul_nonneg (by linarith) (by positivity)) (by norm_num)
  rw [← chaos_polynomial_identity] at h
  linarith

/-- The scalar estimate after multiplying by the squared gradient coefficient. -/
theorem chaos_quadratic_bound_scaled {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2)
    (G : ℝ) :
    chaosQuadratic G (r * G - G / 2) + (7 / 50) * r * G ^ 2 ≤
      (1 - r) * G ^ 2 := by
  have h := mul_le_mul_of_nonneg_right (chaos_quadratic_bound hr0 hr) (sq_nonneg G)
  calc
    _ = (chaosQuadratic 1 (r - 1 / 2) + (7 / 50) * r) * G ^ 2 := by
      unfold chaosQuadratic
      ring
    _ ≤ (1 - r) * G ^ 2 := h

/-- Discarding the two nonnegative remainders in Theorem 3.1. -/
theorem entropy_lower_bound_of_strict_remainder {m : ℕ} {H d energy : ℝ}
    {ell : Fin m → ℝ} (henergy : 0 ≤ energy) (hell : ∀ i, 0 ≤ ell i)
    (h : energy / 500 + (∑ i, rigidityWeight (ell i)) / 1000 ≤
      2 * H - 2 * (m : ℝ) - Real.log d) :
    (m : ℝ) + Real.log d / 2 ≤ H := by
  have hsum : 0 ≤ ∑ i, rigidityWeight (ell i) :=
    Finset.sum_nonneg fun i _ => rigidityWeight_nonneg (hell i)
  linarith

end Submission.Obl.Entropy__lower_bound
