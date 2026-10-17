import Submission.Obl.Entropy__hessian_spectral_surplus.TensorRotation

open scoped BigOperators
open Matrix

namespace Submission.Obl.Entropy__hessian_spectral_surplus

variable {n : Type*} [Fintype n] [DecidableEq n]
open Submission.Lib.PairEstimate

lemma spectral_reconstruct (U M : Matrix n n ℝ) (hU : U * U.transpose = 1)
    (d : n → ℝ) (hd : U.transpose * M * U = Matrix.diagonal d) :
    M = U * Matrix.diagonal d * U.transpose := by
  rw [← hd]
  simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
  rw [Matrix.mul_assoc, hU, Matrix.mul_one]

lemma trace_diagonal_four (u : n → ℝ) (H : Matrix n n ℝ)
    (hH : ∀ i j, H i j = H j i) :
    Matrix.trace (Matrix.diagonal u * H * Matrix.diagonal u * H) =
      ∑ i, ∑ j, u i * u j * H i j ^ 2 := by
  simp only [Matrix.trace, Matrix.diag]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [hH j i]
  ring

lemma trace_diagonal_mixed (k : n → ℝ) (K H : Matrix n n ℝ)
    (hH : ∀ i j, H i j = H j i) :
    Matrix.trace ((K * Matrix.diagonal k + Matrix.diagonal k * K) * H) =
      ∑ i, ∑ j, (k i + k j) * K i j * H i j := by
  simp only [Matrix.trace, Matrix.diag]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply]
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [hH j i]
  ring

lemma first_multiplier_rotation (U M P : Matrix n n ℝ) (H : n → Matrix n n ℝ)
    (hU : U * U.transpose = 1) (p μ : n → ℝ)
    (hP : U.transpose * P * U = Matrix.diagonal p)
    (hM : U.transpose * M * U = Matrix.diagonal μ)
    (hH : ∀ r i j, H r i j = H r j i) :
    (∑ i, ∑ j, P i j * Matrix.trace (M * H i * M * H j)) =
      ∑ r, ∑ i, ∑ j, p r * μ i * μ j * rotateTensor U H r i j ^ 2 := by
  rw [spectral_reconstruct U P hU p hP, trace_contraction_mix]
  apply Finset.sum_congr rfl
  intro r _
  rw [← trace_conjugate U _ hU]
  simp only [conjugate_mul U _ _ hU, hM]
  change p r * Matrix.trace (Matrix.diagonal μ * rotateTensor U H r *
    Matrix.diagonal μ * rotateTensor U H r) = _
  rw [trace_diagonal_four μ _ (rotateTensor_symm_last U H hH r)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma mixTensor_multiplier (U T : Matrix n n ℝ) (K : n → Matrix n n ℝ) (r : n) :
    mixTensor U (fun s => K s * T + T * K s) r =
      mixTensor U K r * T + T * mixTensor U K r := by
  simp only [mixTensor, smul_add, Finset.sum_add_distrib, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul]

lemma second_multiplier_rotation (U M T : Matrix n n ℝ) (H K : n → Matrix n n ℝ)
    (hU : U * U.transpose = 1) (μ k : n → ℝ)
    (hM : U.transpose * M * U = Matrix.diagonal μ)
    (hT : U.transpose * T * U = Matrix.diagonal k)
    (hH : ∀ r i j, H r i j = H r j i) :
    (∑ r, ∑ s, M r s * Matrix.trace ((K s * T + T * K s) * H r)) =
      ∑ r, ∑ i, ∑ j, μ r * (k i + k j) * rotateTensor U K r i j * rotateTensor U H r i j := by
  have hreorder : (∑ r, ∑ s, M r s * Matrix.trace ((K s * T + T * K s) * H r)) =
      ∑ r, ∑ s, M r s * Matrix.trace (1 * H r * 1 * (K s * T + T * K s)) := by
    simp only [Matrix.one_mul, Matrix.mul_one]
    simp only [Matrix.trace_mul_comm (K _ * T + T * K _)]
  rw [hreorder, spectral_reconstruct U M hU μ hM, trace_contraction_mix]
  simp only [Matrix.one_mul, Matrix.mul_one, mixTensor_multiplier]
  apply Finset.sum_congr rfl
  intro r _
  rw [Matrix.trace_mul_comm, ← trace_conjugate U _ hU]
  simp only [conjugate_mul U _ _ hU, Matrix.mul_add, Matrix.add_mul, hT]
  rw [← Matrix.add_mul]
  change μ r * Matrix.trace ((rotateTensor U K r * Matrix.diagonal k +
    Matrix.diagonal k * rotateTensor U K r) * rotateTensor U H r) = _
  rw [trace_diagonal_mixed k _ _ (rotateTensor_symm_last U H hH r)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end Submission.Obl.Entropy__hessian_spectral_surplus
