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

lemma pairing_add_left (A B C : Matrix ι κ ℝ) :
    pairing (A + B) C = pairing A C + pairing B C := by
  simp [pairing, add_mul, Finset.sum_add_distrib]

lemma pairing_add_right (A B C : Matrix ι κ ℝ) :
    pairing A (B + C) = pairing A B + pairing A C := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

lemma pairing_smul_left (c : ℝ) (A B : Matrix ι κ ℝ) :
    pairing (c • A) B = c * pairing A B := by
  simp [pairing, mul_assoc, Finset.mul_sum]

lemma pairing_smul_right (c : ℝ) (A B : Matrix ι κ ℝ) :
    pairing A (c • B) = c * pairing A B := by
  rw [pairing_comm, pairing_smul_left, pairing_comm B A]

lemma squareSum_sub (A B : Matrix ι κ ℝ) :
    squareSum (A - B) = squareSum A + squareSum B - 2 * pairing A B := by
  simp only [squareSum, pairing, Matrix.sub_apply, sub_sq, mul_assoc]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum]
  ring

lemma squareSum_smul (c : ℝ) (A : Matrix ι κ ℝ) :
    squareSum (c • A) = c ^ 2 * squareSum A := by
  simp [squareSum, mul_pow, Finset.mul_sum]

lemma pairing_mul_left {ν : Type*} [Fintype ν]
    (X : Matrix ι κ ℝ) (A : Matrix ι ν ℝ) (B : Matrix κ ν ℝ) :
    pairing A (X * B) = pairing (X.transpose * A) B := by
  rw [pairing_trace, pairing_trace, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.mul_assoc]

lemma pairing_sum_right {ν : Type*} [Fintype ν]
    (A : Matrix ι κ ℝ) (B : ν → Matrix ι κ ℝ) :
    pairing A (∑ r, B r) = ∑ r, pairing A (B r) := by
  simp only [pairing_trace, Matrix.mul_sum, Matrix.trace_sum]

lemma squareSum_mul_right_transpose (A : Matrix ι κ ℝ) :
    Matrix.trace (A * A.transpose) = squareSum A := by
  rw [Matrix.trace_mul_comm, ← squareSum_trace]

/-- A finite family of adjoints has energy given by its row Gram matrix. -/
lemma sum_squareSum_adjoint {ν ρ : Type*} [Fintype ν] [Fintype ρ]
    (X : ν → Matrix ι κ ℝ) (A : Matrix ι ρ ℝ) :
    (∑ r, squareSum ((X r).transpose * A)) =
      pairing A ((∑ r, X r * (X r).transpose) * A) := by
  simp_rw [← pairing_self, ← pairing_mul_left]
  rw [← pairing_sum_right]
  congr 1
  simp only [Matrix.sum_mul, Matrix.mul_assoc]

/-- Weighted energy is nonnegative whenever its left weight is positive semidefinite. -/
lemma weightedSquare_nonneg (P : Matrix ι ι ℝ) (A : Matrix ι κ ℝ)
    (hP : P.PosSemidef) : 0 ≤ pairing A (P * A) := by
  rw [pairing_trace, ← Matrix.mul_assoc]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (hP.conjTranspose_mul_mul_same A).trace_nonneg

/-- Entrywise weighted Young inequality, with a positive weight for every column. -/
lemma pairing_young_columns (A B : Matrix ι κ ℝ) (d : κ → ℝ)
    (hd : ∀ j, 0 < d j) :
    2 * pairing A B ≤
      (∑ i, ∑ j, (A i j) ^ 2 / d j) + (∑ i, ∑ j, d j * (B i j) ^ 2) := by
  have h (a b : ℝ) (j : κ) : 2 * (a * b) ≤ a ^ 2 / d j + d j * b ^ 2 := by
    apply (mul_le_mul_iff_right₀ (hd j)).mp
    rw [mul_add, mul_div_cancel₀ _ (ne_of_gt (hd j))]
    nlinarith [sq_nonneg (a - d j * b)]
  calc
    2 * pairing A B = ∑ i, ∑ j, 2 * (A i j * B i j) := by
      simp [pairing, Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, ((A i j) ^ 2 / d j + d j * (B i j) ^ 2) :=
      Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun j _ => h _ _ j
    _ = _ := by simp [Finset.sum_add_distrib]

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
