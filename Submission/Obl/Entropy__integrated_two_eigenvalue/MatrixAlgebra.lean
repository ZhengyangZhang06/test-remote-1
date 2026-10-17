import Mathlib
import Submission.Lib.EntropyTools.Remainder

open scoped BigOperators

namespace Submission.Obl.Entropy__integrated_two_eigenvalue

open Submission.Lib.EntropyTools Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The entrywise bilinear form is a trace, with no symmetry assumption. -/
lemma entryPairing_eq_trace (M N : Matrix n n ℝ) :
    (∑ i, ∑ j, M i j * N i j) = Matrix.trace (M.transpose * N) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- A pointwise orthogonal change of eigenbasis preserves the entrywise bilinear form. -/
lemma entryPairing_orthogonal (U M N : Matrix n n ℝ)
    (hU : U * U.transpose = 1) :
    (∑ i, ∑ j, (U.transpose*M*U) i j * (U.transpose*N*U) i j) =
      ∑ i, ∑ j, M i j * N i j := by
  rw [entryPairing_eq_trace, entryPairing_eq_trace]
  calc
    _ = Matrix.trace (U.transpose * (M.transpose * (U*U.transpose) * N) * U) := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
      congr 1
      noncomm_ring
    _ = Matrix.trace (U.transpose * (M.transpose*N) * U) := by rw [hU]; simp
    _ = Matrix.trace (U * U.transpose * (M.transpose*N)) := by
      rw [Matrix.trace_mul_cycle]
    _ = _ := by rw [hU]; simp

lemma squareSum_orthogonal (U M : Matrix n n ℝ) (hU : U * U.transpose = 1) :
    (∑ i, ∑ j, ((U.transpose*M*U) i j)^2) = ∑ i, ∑ j, (M i j)^2 := by
  simpa only [pow_two] using entryPairing_orthogonal U M M hU

lemma chaosQuadratic_shift (G g : ℝ) :
    chaosQuadratic G (g-G/2) = (49/50)*G^2 - (123/50)*G*g + (68/25)*g^2 := by
  unfold chaosQuadratic
  ring

lemma chaosQuadratic_sum (G g : Matrix n n ℝ) :
    (∑ i, ∑ j, chaosQuadratic (G i j) (g i j-G i j/2)) =
      (49/50)*(∑ i, ∑ j, (G i j)^2) -
      (123/50)*(∑ i, ∑ j, G i j*g i j) +
      (68/25)*(∑ i, ∑ j, (g i j)^2) := by
  simp only [chaosQuadratic_shift, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← mul_assoc, Finset.mul_sum]

/-- The quadratic energy can be returned to fixed coordinates after the pointwise estimate. -/
lemma chaosQuadratic_orthogonal (U G g : Matrix n n ℝ) (hU : U*U.transpose = 1) :
    (∑ i, ∑ j, chaosQuadratic ((U.transpose*G*U) i j)
      ((U.transpose*g*U) i j-(U.transpose*G*U) i j/2)) =
      ∑ i, ∑ j, chaosQuadratic (G i j) (g i j-G i j/2) := by
  rw [chaosQuadratic_sum, chaosQuadratic_sum,
    squareSum_orthogonal U G hU, squareSum_orthogonal U g hU,
    entryPairing_orthogonal U G g hU]

/-- Summing endpoint averages is the same as summing entries. -/
lemma sum_transpose_average (F : Matrix n n ℝ) :
    (∑ i, ∑ j, (F i j+F j i)/2) = ∑ i, ∑ j, F i j := by
  simp only [add_div, Finset.sum_add_distrib, ← Finset.sum_div]
  rw [Finset.sum_comm (f := fun i j => F j i)]
  ring

/-- Pair the transposed entries before applying the two-eigenvalue estimate. -/
lemma sum_le_of_transpose_average (F H : Matrix n n ℝ)
    (h : ∀ i j, (F i j+F j i)/2 ≤ H i j) :
    (∑ i, ∑ j, F i j) ≤ ∑ i, ∑ j, H i j := by
  rw [← sum_transpose_average F]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j

end Submission.Obl.Entropy__integrated_two_eigenvalue
