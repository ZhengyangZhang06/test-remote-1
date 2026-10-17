/-
Adapted from: here:o017

Original Section 4 and matrix-algebra proofs by session x0043.
-/

import Submission.Lib.PairEstimate.MatrixAlgebra

open scoped BigOperators

namespace Submission.Lib.PairEstimate

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma eigenbasis_transpose_mul_self {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℝ).transpose * hA.eigenvectorUnitary = 1 := by
  simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    Unitary.coe_star_mul_self hA.eigenvectorUnitary

lemma eigenbasis_mul_transpose_self {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℝ) *
      (hA.eigenvectorUnitary : Matrix n n ℝ).transpose = 1 := by
  simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    Unitary.coe_mul_star_self hA.eigenvectorUnitary

/-- The canonical eigenbasis diagonalizes every scalar function, even at repeated eigenvalues. -/
lemma cfc_in_eigenbasis {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (hA.eigenvectorUnitary : Matrix n n ℝ).transpose * cfc f A * hA.eigenvectorUnitary =
      Matrix.diagonal (fun i => f (hA.eigenvalues i)) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hU := eigenbasis_transpose_mul_self hA
  simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
  rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  rfl

lemma conjugate_mul (U M N : Matrix n n ℝ) (hU : U*U.transpose = 1) :
    U.transpose*(M*N)*U = (U.transpose*M*U)*(U.transpose*N*U) := by
  calc
    _ = U.transpose*M*(U*U.transpose)*N*U := by rw [hU]; simp [Matrix.mul_assoc]
    _ = _ := by noncomm_ring

lemma cfc_right_in_eigenbasis {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (M : Matrix n n ℝ) (f : ℝ → ℝ) (i j : n) :
    ((hA.eigenvectorUnitary : Matrix n n ℝ).transpose * (M*cfc f A) *
      hA.eigenvectorUnitary) i j =
    ((hA.eigenvectorUnitary : Matrix n n ℝ).transpose * M *
      hA.eigenvectorUnitary) i j * f (hA.eigenvalues j) := by
  rw [conjugate_mul _ _ _ (eigenbasis_mul_transpose_self hA), cfc_in_eigenbasis]
  simp only [Matrix.mul_diagonal]

/-- Right multiplication by p(A)^(-1/2) yields exactly the column denominator p_j. -/
lemma weighted_squareSum_in_eigenbasis {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (M : Matrix n n ℝ) (p : ℝ → ℝ) (hp : ∀ a, 0 < p a) :
    (∑ i, ∑ j, ((M*cfc (fun a => (Real.sqrt (p a))⁻¹) A) i j)^2) =
      ∑ i, ∑ j,
        (((hA.eigenvectorUnitary : Matrix n n ℝ).transpose * M *
          hA.eigenvectorUnitary) i j)^2 / p (hA.eigenvalues j) := by
  rw [← squareSum_orthogonal _ _ (eigenbasis_mul_transpose_self hA)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [cfc_right_in_eigenbasis, mul_pow, inv_pow, Real.sq_sqrt (hp _).le, div_eq_mul_inv]

end Submission.Lib.PairEstimate
