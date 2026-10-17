/-
Adapted from: here:o006
Original matrix functional-calculus derivative proofs by session x0063.
-/

import Submission.Obl.Entropy__c1_bounded_matrix_calculus.CFCEntry
import Submission.Lib.MatrixEntropy.Squares

open scoped BigOperators Matrix.Norms.L2Operator

namespace Submission.Obl.Entropy__c1_bounded_matrix_calculus

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared Frobenius norm, without a choice of a matrix norm instance. -/
def matrixSquareSum (H : Matrix n n ℝ) : ℝ := ∑ i, ∑ j, (H i j)^2

omit [DecidableEq n] in
lemma matrixSquareSum_eq_trace (H : Matrix n n ℝ) :
    matrixSquareSum H = (H.transpose * H).trace := by
  simp only [matrixSquareSum, Submission.Lib.MatrixEntropy.trace_transpose_mul, pow_two]

lemma matrixSquareSum_conj (U : Matrix.unitaryGroup n ℝ) (H : Matrix n n ℝ) :
    matrixSquareSum (Unitary.conjStarAlgAut ℝ _ U H) = matrixSquareSum H := by
  let e := Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) U
  have ht : (e H).transpose = e H.transpose := by
    simpa only [← Matrix.conjTranspose_eq_transpose_of_trivial,
      ← Matrix.star_eq_conjTranspose] using (map_star e H).symm
  rw [matrixSquareSum_eq_trace, matrixSquareSum_eq_trace]
  change ((e H).transpose * e H).trace = _
  rw [ht, ← map_mul]
  change (Unitary.conjStarAlgAut ℝ _ U (H.transpose * H)).trace = _
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

lemma matrixSquareSum_eigenbasis {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (H : Matrix n n ℝ) :
    matrixSquareSum ((Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary).symm H) =
      matrixSquareSum H := by
  rw [Unitary.conjStarAlgAut_symm]
  exact matrixSquareSum_conj _ _

/-- A divided-difference bound gives the exact Frobenius derivative bound. -/
lemma spectralDerivative_squareSum_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (H : Matrix n n ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ i j, |dslope f (hA.eigenvalues i) (hA.eigenvalues j)| ≤ C) :
    matrixSquareSum (spectralDerivative hA f H) ≤ C^2 * matrixSquareSum H := by
  rw [← matrixSquareSum_eigenbasis hA (spectralDerivative hA f H),
    ← matrixSquareSum_eigenbasis hA H]
  simp only [matrixSquareSum, spectralDerivative_eigenbasis, Finset.mul_sum, mul_pow]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (abs_nonneg _) hC).2 (hbound i j) |>
    (by simpa only [sq_abs] using ·)) (sq_nonneg _)

/-- Scalar derivative bounds on a convex interval also bound its divided differences. -/
lemma abs_dslope_le_of_deriv_bound {f : ℝ → ℝ} {s : Set ℝ} (hs : Convex ℝ s)
    (hf : Differentiable ℝ f) {C a b : ℝ}
    (hbound : ∀ t ∈ s, |deriv f t| ≤ C) (ha : a ∈ s) (hb : b ∈ s) :
    |dslope f a b| ≤ C := by
  by_cases h : b = a
  · subst b
    simpa only [dslope_same] using hbound a ha
  · rw [dslope_of_ne f h, slope_def_field, abs_div]
    apply (div_le_iff₀ (abs_pos.2 (sub_ne_zero.2 h))).2
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_deriv_le (fun t _ => hf t)
        (by simpa only [Real.norm_eq_abs] using hbound) hs ha hb

lemma spectralDerivative_squareSum_le_of_deriv_bound {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (H : Matrix n n ℝ) {s : Set ℝ} (hs : Convex ℝ s) (hspec : spectrum ℝ A ⊆ s)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ t ∈ s, |deriv f t| ≤ C) :
    matrixSquareSum (spectralDerivative hA f H) ≤ C^2 * matrixSquareSum H := by
  apply spectralDerivative_squareSum_le hA f H hC
  intro i j
  exact abs_dslope_le_of_deriv_bound hs hf hbound
    (hspec (hA.eigenvalues_mem_spectrum_real i))
    (hspec (hA.eigenvalues_mem_spectrum_real j))

/-- A continuously differentiable scalar function has a uniform divided-difference
bound on each compact interval. -/
lemma exists_dslope_bound_Icc {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (a b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
      |dslope f u v| ≤ C := by
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image
    (hf.continuous_deriv (by norm_num)).abs.continuousOn
  refine ⟨max K 0 + 1, by positivity, ?_⟩
  intro u hu v hv
  apply abs_dslope_le_of_deriv_bound (convex_Icc a b) (hf.differentiable (by norm_num))
    (fun t ht => ?_) hu hv
  exact (hK ⟨t, ht, rfl⟩).trans (by linarith [le_max_left K 0])

end Submission.Obl.Entropy__c1_bounded_matrix_calculus
