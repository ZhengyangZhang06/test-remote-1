/-
Adapted from: here:o006

Original proofs by session x0016.
-/

import Mathlib

/-!
# The scalar quadratic bound in Lemma 3.4

The `1 + s/8` constant in the matrix commutator estimate comes from
these two-variable inequalities. No spectral choices occur here.
-/

namespace Submission.Lib.EntropyRemainder

/-- The sharp off-diagonal bound for the two-by-two block in Lemma 3.4. -/
theorem commutator_sqrt_bound {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.sqrt (u * v * (1 - u) * (1 - v)) ≤ u * v + 1 / 8 := by
  let z := Real.sqrt (u * v)
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hz2 : z ^ 2 = u * v := Real.sq_sqrt (mul_nonneg hu hv)
  have huv : 2 * z ≤ u + v := by nlinarith [sq_nonneg (u - v)]
  have hpoly : 0 ≤ u * v * (u + v - 3 / 4) + 1 / 64 := by
    calc
      0 ≤ (z - 1 / 4) ^ 2 * (2 * z + 1 / 4) := by positivity
      _ = z ^ 2 * (2 * z - 3 / 4) + 1 / 64 := by ring
      _ ≤ z ^ 2 * (u + v - 3 / 4) + 1 / 64 := by gcongr
      _ = u * v * (u + v - 3 / 4) + 1 / 64 := by rw [hz2]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith

/-- The full scalar block, including the diagonal `-suv` contribution. -/
theorem commutator_pair_bound {s u v : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (a b : ℝ) :
    (1 - s * u * v) * (a ^ 2 + b ^ 2) -
      2 * s * Real.sqrt (u * v * (1 - u) * (1 - v)) * a * b ≤
      (1 + s / 8) * (a ^ 2 + b ^ 2) := by
  have hsq := mul_nonneg
    (mul_nonneg hs (Real.sqrt_nonneg (u * v * (1 - u) * (1 - v)))) (sq_nonneg (a + b))
  have hbound := mul_le_mul_of_nonneg_right (commutator_sqrt_bound hu hv)
    (mul_nonneg hs (add_nonneg (sq_nonneg a) (sq_nonneg b)))
  nlinarith

end Submission.Lib.EntropyRemainder
