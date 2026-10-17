import Mathlib

open scoped BigOperators

namespace Submission.Obl.Entropy__noncommuting_remainder_assembly

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The squared Frobenius norm, without choosing a matrix norm instance. -/
def squareSum (A : Matrix ι κ ℝ) : ℝ := ∑ i, ∑ j, (A i j) ^ 2

/-- The real Frobenius pairing. -/
def pairing (A B : Matrix ι κ ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

lemma squareSum_nonneg (A : Matrix ι κ ℝ) : 0 ≤ squareSum A := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma pairing_self (A : Matrix ι κ ℝ) : pairing A A = squareSum A := by
  simp [pairing, squareSum, pow_two]

lemma pairing_comm (A B : Matrix ι κ ℝ) : pairing A B = pairing B A := by
  simp [pairing, mul_comm]

lemma pairing_trace (A B : Matrix ι κ ℝ) :
    pairing A B = Matrix.trace (A.transpose * B) := by
  simp only [pairing, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  exact Finset.sum_comm

lemma squareSum_trace (A : Matrix ι κ ℝ) :
    squareSum A = Matrix.trace (A.transpose * A) := by
  rw [← pairing_self, pairing_trace]

lemma pairing_young (A B : Matrix ι κ ℝ) {c : ℝ} (hc : 0 < c) :
    pairing A B ≤ c * squareSum A + squareSum B / (4 * c) := by
  have h (a b : ℝ) : a * b ≤ c * a ^ 2 + b ^ 2 / (4 * c) := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 4 * c)).mp
    field_simp
    nlinarith [sq_nonneg (2 * c * a - b)]
  calc
    pairing A B ≤ ∑ i, ∑ j, (c * (A i j) ^ 2 + (B i j) ^ 2 / (4 * c)) :=
      Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => h _ _
    _ = c * squareSum A + squareSum B / (4 * c) := by
      simp [squareSum, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]

/-- The cubic inequality behind the sharp commutator coefficient. -/
lemma commutator_cubic {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    u * v * (3 / 4 - u - v) ≤ 1 / 64 := by
  by_cases huv : 3 / 4 ≤ u + v
  · have h := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hu hv)
      (show 3 / 4 - u - v ≤ 0 by linarith)
    linarith
  · have h₁ := mul_nonneg (sq_nonneg (u + v - 1 / 2))
      (show 0 ≤ u + v + 1 / 4 by linarith)
    have h₂ := mul_nonneg (sq_nonneg (u - v))
      (show 0 ≤ 3 / 4 - (u + v) by linarith)
    nlinarith

lemma commutator_coefficient {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    v * (1 - u) / (v + 1 / 8) + u * (1 - v) / (u + 1 / 8) ≤ 1 := by
  have hu' : 0 < u + 1 / 8 := by linarith
  have hv' : 0 < v + 1 / 8 := by linarith
  rw [div_add_div _ _ (ne_of_gt hv') (ne_of_gt hu'), div_le_one (mul_pos hv' hu')]
  nlinarith [commutator_cubic hu hv]

end Submission.Obl.Entropy__noncommuting_remainder_assembly
