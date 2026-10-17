import Submission.Obl.Entropy__hessian_spectral_surplus.SpectralMeasurable

open scoped BigOperators Topology
open Matrix Filter MeasureTheory

namespace Submission.Obl.Entropy__hessian_spectral_surplus

variable {n : Type*} [Fintype n] [DecidableEq n]
open Submission.Lib.PairEstimate

/-- Repeated commutation produces powers of eigenvalue differences. -/
def iterComm (L Z : Matrix n n ℝ) : ℕ → Matrix n n ℝ
  | 0 => Z
  | k + 1 => L * iterComm L Z k - iterComm L Z k * L

lemma iterComm_in_eigenbasis {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (Z : Matrix n n ℝ) (k : ℕ) (i j : n) :
    let U : Matrix n n ℝ := hA.eigenvectorUnitary
    (U.transpose * iterComm (cfc f A) Z k * U) i j =
      (f (hA.eigenvalues i) - f (hA.eigenvalues j)) ^ k *
        (U.transpose * Z * U) i j := by
  dsimp only
  induction k with
  | zero => simp [iterComm]
  | succ k ih =>
    simp only [iterComm, Matrix.mul_sub, Matrix.sub_mul]
    rw [conjugate_mul _ _ _ (eigenbasis_mul_transpose_self hA),
      conjugate_mul _ _ _ (eigenbasis_mul_transpose_self hA), cfc_in_eigenbasis]
    simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [ih, pow_succ]
    ring

lemma cutoff_commutator_squareSum {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (c : ℝ) (Z : Matrix n n ℝ) (k : ℕ) :
    let U : Matrix n n ℝ := hA.eigenvectorUnitary
    let P : Matrix n n ℝ := cfc (fun t : ℝ => if c ≤ t then 1 else 0) A
    (∑ i, ∑ j, (P * iterComm (cfc f A) Z k * P) i j ^ 2) =
      ∑ i, ∑ j, (if c ≤ min (hA.eigenvalues i) (hA.eigenvalues j) then 1 else 0) *
        (f (hA.eigenvalues i) - f (hA.eigenvalues j)) ^ (2 * k) *
          (U.transpose * Z * U) i j ^ 2 := by
  dsimp only
  rw [← squareSum_orthogonal _ _ (eigenbasis_mul_transpose_self hA)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [conjugate_mul _ _ _ (eigenbasis_mul_transpose_self hA),
    conjugate_mul _ _ _ (eigenbasis_mul_transpose_self hA), cfc_in_eigenbasis]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [iterComm_in_eigenbasis]
  by_cases hi : c ≤ hA.eigenvalues i <;> by_cases hj : c ≤ hA.eigenvalues j <;>
    simp [hi, hj, le_min_iff, mul_pow, ← pow_mul, Nat.mul_comm]

lemma commutator_squareSum {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (Z : Matrix n n ℝ) (k : ℕ) :
    let U : Matrix n n ℝ := hA.eigenvectorUnitary
    (∑ i, ∑ j, iterComm (cfc f A) Z k i j ^ 2) =
      ∑ i, ∑ j, (f (hA.eigenvalues i) - f (hA.eigenvalues j)) ^ (2 * k) *
        (U.transpose * Z * U) i j ^ 2 := by
  dsimp only
  rw [← squareSum_orthogonal _ _ (eigenbasis_mul_transpose_self hA)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [iterComm_in_eigenbasis, mul_pow, ← pow_mul, Nat.mul_comm]

variable {X : Type*} [MeasurableSpace X]

lemma measurable_matrix_mul_entries {M N : X → Matrix n n ℝ}
    (hM : ∀ i j, Measurable (fun x => M x i j))
    (hN : ∀ i j, Measurable (fun x => N x i j)) (i j : n) :
    Measurable (fun x => (M x * N x) i j) := by
  exact Finset.measurable_sum _ (fun s _ => (hM i s).mul (hN s j))

lemma measurable_iterComm_entries {L Z : X → Matrix n n ℝ}
    (hL : ∀ i j, Measurable (fun x => L x i j))
    (hZ : ∀ i j, Measurable (fun x => Z x i j)) (k : ℕ) (i j : n) :
    Measurable (fun x => iterComm (L x) (Z x) k i j) := by
  induction k generalizing i j with
  | zero => exact hZ i j
  | succ k ih => exact
      (measurable_matrix_mul_entries hL ih i j).sub (measurable_matrix_mul_entries ih hL i j)

end Submission.Obl.Entropy__hessian_spectral_surplus
