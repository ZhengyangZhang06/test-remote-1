/-
Adapted from: here:o030
Original proof by session x0091.
-/

import Mathlib
import Submission.Lib.PairEstimate.SpectralAlgebra

open scoped BigOperators
open Matrix

namespace Submission.Lib.MatrixCFCDerivative

variable {n : Type*} [Fintype n] [DecidableEq n]

open Submission.Lib.PairEstimate

/-- The left eigenvector identity for an arbitrary scalar spectral function. -/
lemma eigenbasis_left_cfc {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) :
    (hA.eigenvectorUnitary : Matrix n n ℝ).transpose * cfc f A =
      Matrix.diagonal (fun i => f (hA.eigenvalues i)) *
        (hA.eigenvectorUnitary : Matrix n n ℝ).transpose := by
  have h := congrArg (fun M : Matrix n n ℝ =>
    M * (hA.eigenvectorUnitary : Matrix n n ℝ).transpose) (cfc_in_eigenbasis hA f)
  simpa only [Matrix.mul_assoc, eigenbasis_mul_transpose_self hA, Matrix.mul_one] using h

lemma eigenbasis_left_matrix {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℝ).transpose * A =
      Matrix.diagonal hA.eigenvalues *
        (hA.eigenvectorUnitary : Matrix n n ℝ).transpose := by
  simpa only [cfc_id ℝ A hA.isSelfAdjoint, id_eq] using eigenbasis_left_cfc hA id

/-- Functional calculus turns the scalar divided-difference identity into a matrix identity. -/
lemma cfc_sub_eq_mul_dslope {B : Matrix n n ℝ} (hB : B.IsHermitian)
    (f : ℝ → ℝ) (a : ℝ) :
    cfc f B - algebraMap ℝ (Matrix n n ℝ) (f a) =
      (B - algebraMap ℝ (Matrix n n ℝ) a) * cfc (dslope f a) B := by
  have hc (g : ℝ → ℝ) : ContinuousOn g (spectrum ℝ B) :=
    B.finite_real_spectrum.continuousOn g
  calc
    _ = cfc (fun x : ℝ => f x - f a) B := by
      rw [cfc_sub _ _ B (hc _) (hc _), cfc_const _ B hB.isSelfAdjoint]
    _ = cfc (fun x : ℝ => (x - a) * dslope f a x) B := by
      congr 1
      funext b
      exact (sub_smul_dslope f a b).symm
    _ = _ := by
      rw [cfc_mul _ _ B (hc _) (hc _), cfc_sub _ _ B (hc _) (hc _),
        cfc_const _ B hB.isSelfAdjoint]
      rw [show (fun x : ℝ => x) = id from rfl, cfc_id ℝ B hB.isSelfAdjoint]

/-- Exact first-order difference identity in the eigenbasis of the base matrix. -/
lemma cfc_difference_row {A B : Matrix n n ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (f : ℝ → ℝ) (i j : n) :
    ((hA.eigenvectorUnitary : Matrix n n ℝ).transpose * (cfc f B - cfc f A)) i j =
    ((hA.eigenvectorUnitary : Matrix n n ℝ).transpose * (B - A) *
      cfc (dslope f (hA.eigenvalues i)) B) i j := by
  let U : Matrix n n ℝ := hA.eigenvectorUnitary
  let G : Matrix n n ℝ := cfc (dslope f (hA.eigenvalues i)) B
  have hG := cfc_sub_eq_mul_dslope hB f (hA.eigenvalues i)
  have hG' : B * G = cfc f B - (f (hA.eigenvalues i)) • 1 +
      (hA.eigenvalues i) • G := by
    simpa only [Matrix.sub_mul, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
      Matrix.one_mul, sub_eq_iff_eq_add] using hG.symm
  change (U.transpose * (cfc f B - cfc f A)) i j =
    (U.transpose * (B - A) * G) i j
  simp only [Matrix.mul_sub, Matrix.sub_mul]
  rw [Matrix.mul_assoc U.transpose B G, hG']
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
  have hAf := eigenbasis_left_cfc hA f
  have hAx := eigenbasis_left_matrix hA
  change U.transpose * cfc f A = _ at hAf
  change U.transpose * A = _ at hAx
  rw [hAf, hAx, Matrix.mul_assoc]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.diagonal_mul]
  ring

end Submission.Lib.MatrixCFCDerivative
