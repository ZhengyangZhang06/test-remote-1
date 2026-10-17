import Submission.Obl.Entropy__noncommuting_remainder_assembly.Block

open scoped BigOperators

namespace Submission.Obl.Entropy__noncommuting_remainder_assembly

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

lemma pairing_mul_right_cancel [DecidableEq ι]
    (A B : Matrix κ ι ℝ) (P R : Matrix ι ι ℝ)
    (hRP : R * P.transpose = 1) :
    pairing (A * P) (B * R) = pairing A B := by
  rw [pairing_trace, Matrix.transpose_mul, pairing_trace]
  calc
    Matrix.trace (P.transpose * A.transpose * (B * R)) =
        Matrix.trace (R * P.transpose * (A.transpose * B)) := by
      simpa only [Matrix.mul_assoc] using
        Matrix.trace_mul_comm (P.transpose * (A.transpose * B)) R
    _ = Matrix.trace (A.transpose * B) := by rw [hRP, Matrix.one_mul]

lemma pairing_weight_right (T P : Matrix ι ι ℝ) (B : Matrix ι ι ℝ) :
    pairing (T * P) (B * (T * P)) =
      Matrix.trace ((T.transpose * B * T) * (P * P.transpose)) := by
  rw [pairing_trace, Matrix.transpose_mul]
  simpa only [Matrix.mul_assoc] using
    Matrix.trace_mul_comm P.transpose (T.transpose * B * T * P)

lemma squareSum_mul_right (T P : Matrix ι ι ℝ) :
    squareSum (T * P) =
      Matrix.trace ((T.transpose * T) * (P * P.transpose)) := by
  rw [squareSum_trace, Matrix.transpose_mul]
  simpa only [Matrix.mul_assoc] using
    Matrix.trace_mul_comm P.transpose (T.transpose * T * P)

/-- Weighted completion without a pseudoinverse: apply Young to each block. -/
lemma weighted_completion [DecidableEq ι]
    (X : ν → Matrix ι κ ℝ) (T a P R : Matrix ι ι ℝ)
    (M : ν → Matrix κ ι ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hRP : R * P.transpose = 1) :
    pairing T (a + ∑ r, X r * M r) ≤
      Matrix.trace ((c • (T.transpose * T) +
        d • (T.transpose * (∑ r, X r * (X r).transpose) * T)) *
          (P * P.transpose)) +
      squareSum (a * R) / (4 * c) + (∑ r, squareSum (M r * R)) / (4 * d) := by
  have ha := pairing_young (T * P) (a * R) hc
  have hM := Finset.sum_le_sum (s := Finset.univ)
    (fun r _ => pairing_young (((X r).transpose * T) * P) (M r * R) hd)
  rw [pairing_mul_right_cancel T a P R hRP] at ha
  simp_rw [pairing_mul_right_cancel _ _ P R hRP, ← pairing_mul_left,
    Matrix.mul_assoc] at hM
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div] at hM
  have henergy : c * squareSum (T * P) +
      d * (∑ r, squareSum ((X r).transpose * (T * P))) =
        Matrix.trace ((c • (T.transpose * T) +
          d • (T.transpose * (∑ r, X r * (X r).transpose) * T)) *
            (P * P.transpose)) := by
    rw [sum_squareSum_adjoint, pairing_weight_right, squareSum_mul_right]
    simp [Matrix.add_mul]
  rw [pairing_add_right, pairing_sum_right]
  linarith

/-- The exact coefficients used by the remainder assembly. -/
lemma weighted_completion_constants [DecidableEq ι]
    (X : ν → Matrix ι κ ℝ) (T a P R : Matrix ι ι ℝ)
    (M : ν → Matrix κ ι ℝ) (hRP : R * P.transpose = 1) :
    pairing T (a + ∑ r, X r * M r) ≤
      Matrix.trace (((111 / 25 : ℝ) • (T.transpose * T) +
        (17 / 20 : ℝ) • (T.transpose * (∑ r, X r * (X r).transpose) * T)) *
          (P * P.transpose)) +
      (40 / 37 : ℝ) * (5 / 96 : ℝ) * squareSum (a * R) +
      (5 / 17 : ℝ) * (∑ r, squareSum (M r * R)) := by
  have h := weighted_completion X T a P R M (c := 111 / 25) (d := 17 / 20)
    (by norm_num) (by norm_num) hRP
  convert h using 1; ring

end Submission.Obl.Entropy__noncommuting_remainder_assembly
