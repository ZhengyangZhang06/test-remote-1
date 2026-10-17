/-
Adapted from: here:o006

Original proofs by session x0016.
-/

import Mathlib

/-!
# The block-operator argument behind the weighted Cauchy--Schwarz bound

A matrix whose rows are orthonormal contracts the entry-square norm.
This is the algebraic fact used in the two block bounds of Section 3.
-/

namespace Submission.Lib.EntropyRemainder

open scoped BigOperators

/-- The complement of the projection onto a matrix's orthonormal rows is positive. -/
theorem rowIsometry_complement_posSemidef
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {M : Matrix m n ℝ} (hM : M * M.conjTranspose = 1) :
    (1 - M.conjTranspose * M).PosSemidef := by
  have hQ : (M.conjTranspose * M) * (M.conjTranspose * M) = M.conjTranspose * M := by
    calc
      _ = M.conjTranspose * (M * M.conjTranspose) * M := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hM, Matrix.mul_one]
  have hP : (1 - M.conjTranspose * M).IsHermitian :=
    Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_self M)
  have hP2 : (1 - M.conjTranspose * M) * (1 - M.conjTranspose * M) =
      1 - M.conjTranspose * M := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul, hQ]
    abel
  have hpos := Matrix.posSemidef_conjTranspose_mul_self (1 - M.conjTranspose * M)
  rw [hP.eq, hP2] at hpos
  exact hpos

/-- A coisometric block operator contracts the squared Frobenius norm. -/
theorem rowIsometry_trace_contraction
    {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq m] [DecidableEq n]
    {M : Matrix m n ℝ} (hM : M * M.conjTranspose = 1) (N : Matrix n k ℝ) :
    Matrix.trace ((M * N).conjTranspose * (M * N)) ≤
      Matrix.trace (N.conjTranspose * N) := by
  have h := ((rowIsometry_complement_posSemidef hM).conjTranspose_mul_mul_same N).trace_nonneg
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.trace_sub] at h
  have heq : N.conjTranspose * (M.conjTranspose * M) * N =
      (M * N).conjTranspose * (M * N) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [heq] at h
  linarith

/-- The same contraction in the entry-square convention of the frozen statement. -/
theorem rowIsometry_entry_contraction
    {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq m] [DecidableEq n]
    {M : Matrix m n ℝ} (hM : M * M.conjTranspose = 1) (N : Matrix n k ℝ) :
    (∑ j, ∑ i, (M * N) i j ^ 2) ≤ ∑ j, ∑ i, N i j ^ 2 := by
  simpa only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    star_trivial, ← pow_two] using rowIsometry_trace_contraction hM N

end Submission.Lib.EntropyRemainder
