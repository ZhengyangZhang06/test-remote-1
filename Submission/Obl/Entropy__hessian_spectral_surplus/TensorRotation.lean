import Submission.Lib.PairEstimate.SpectralAlgebra

open scoped BigOperators
open Matrix

namespace Submission.Obl.Entropy__hessian_spectral_surplus

variable {n : Type*} [Fintype n] [DecidableEq n]
open Submission.Lib.PairEstimate

noncomputable def mixTensor (U : Matrix n n ℝ) (H : n → Matrix n n ℝ) (r : n) : Matrix n n ℝ :=
  ∑ a, U a r • H a

noncomputable def rotateTensor (U : Matrix n n ℝ) (H : n → Matrix n n ℝ) (r : n) : Matrix n n ℝ :=
  U.transpose * mixTensor U H r * U

lemma sum3_cycle (F : n → n → n → ℝ) :
    (∑ i, ∑ j, ∑ r, F i j r) = ∑ r, ∑ i, ∑ j, F i j r := by
  calc
    _ = ∑ i, ∑ r, ∑ j, F i j r := Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

lemma sum3_rotate (F : n → n → n → ℝ) :
    (∑ r, ∑ i, ∑ j, F r i j) = ∑ i, ∑ j, ∑ r, F r i j := by
  calc
    _ = ∑ i, ∑ r, ∑ j, F r i j := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun i _ => Finset.sum_comm)

/-- A diagonal coefficient rotates both slots of a trace contraction. -/
lemma trace_contraction_mix (U L M : Matrix n n ℝ) (w : n → ℝ)
    (H K : n → Matrix n n ℝ) :
    (∑ i, ∑ j, (U * Matrix.diagonal w * U.transpose) i j * Matrix.trace (L * H i * M * K j)) =
      ∑ r, w r * Matrix.trace (L * mixTensor U H r * M * mixTensor U K r) := by
  have hentry (i j : n) : (U * Matrix.diagonal w * U.transpose) i j =
      ∑ r, U i r * w r * U j r := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  simp only [hentry, Finset.sum_mul,
    mixTensor, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
  rw [sum3_cycle]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma trace_conjugate (U M : Matrix n n ℝ) (hU : U * U.transpose = 1) :
    Matrix.trace (U.transpose * M * U) = Matrix.trace M := by
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]

lemma rotateTensor_apply (U : Matrix n n ℝ) (H : n → Matrix n n ℝ) (r i j : n) :
    rotateTensor U H r i j = ∑ a, ∑ b, ∑ c, U a r * U b i * U c j * H a b c := by
  simp only [rotateTensor, mixTensor, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

lemma rotateTensor_symm_last (U : Matrix n n ℝ) (H : n → Matrix n n ℝ)
    (hH : ∀ r i j, H r i j = H r j i) (r i j : n) :
    rotateTensor U H r i j = rotateTensor U H r j i := by
  rw [rotateTensor_apply, rotateTensor_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [hH a b c]
  ring

lemma rotateTensor_symm_first (U : Matrix n n ℝ) (H : n → Matrix n n ℝ)
    (hH : ∀ r i j, H r i j = H i r j) (r i j : n) :
    rotateTensor U H r i j = rotateTensor U H i r j := by
  rw [rotateTensor_apply, rotateTensor_apply, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [hH b a c]
  ring

lemma orthogonal_sum_mul (U : Matrix n n ℝ) (hU : U * U.transpose = 1) (v w : n → ℝ) :
    (∑ r, (∑ a, U a r * v a) * (∑ b, U b r * w b)) = ∑ a, v a * w a := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [sum3_rotate, Finset.sum_comm]
  calc
    _ = ∑ a, ∑ b, (U * U.transpose) a b * (v a * w b) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by simp [hU, Matrix.one_apply]

lemma rotateTensor_energy (U : Matrix n n ℝ) (hU : U * U.transpose = 1)
    (H : n → Matrix n n ℝ) :
    (∑ r, ∑ i, ∑ j, rotateTensor U H r i j ^ 2) = ∑ r, ∑ i, ∑ j, H r i j ^ 2 := by
  calc
    _ = ∑ r, ∑ i, ∑ j, mixTensor U H r i j ^ 2 := by
      apply Finset.sum_congr rfl
      intro r _
      exact squareSum_orthogonal U (mixTensor U H r) hU
    _ = ∑ i, ∑ j, ∑ r, mixTensor U H r i j ^ 2 := sum3_rotate _
    _ = ∑ i, ∑ j, ∑ r, H r i j ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simpa only [mixTensor, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, pow_two] using
        orthogonal_sum_mul U hU (fun r => H r i j) (fun r => H r i j)
    _ = _ := (sum3_rotate _).symm


lemma rotateTensor_entry (U : Matrix n n ℝ) (H : n → Matrix n n ℝ) (r i j : n) :
    rotateTensor U H r i j = ∑ a, U a r * (U.transpose * H a * U) i j := by
  simp only [rotateTensor, mixTensor, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

lemma rotateTensor_weighted_energy (U : Matrix n n ℝ) (hU : U * U.transpose = 1)
    (Z : n → Matrix n n ℝ) (w : n → n → ℝ) :
    (∑ r, ∑ i, ∑ j, w i j * rotateTensor U Z r i j ^ 2) =
      ∑ r, ∑ i, ∑ j, w i j * (U.transpose * Z r * U) i j ^ 2 := by
  calc
    _ = ∑ i, ∑ j, ∑ r, w i j * rotateTensor U Z r i j ^ 2 := sum3_rotate _
    _ = ∑ i, ∑ j, ∑ r, w i j * (U.transpose * Z r * U) i j ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [← Finset.mul_sum, rotateTensor_entry]
      congr 1
      simpa only [pow_two] using orthogonal_sum_mul U hU
        (fun r => (U.transpose * Z r * U) i j) (fun r => (U.transpose * Z r * U) i j)
    _ = _ := (sum3_rotate _).symm

end Submission.Obl.Entropy__hessian_spectral_surplus
