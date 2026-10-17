import Mathlib

namespace Submission.Obl.Entropy__equality_cases

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The square of the Frobenius norm, expressed without choosing a matrix norm instance. -/
def frobeniusSq (M : Matrix ι ι ℝ) : ℝ := (M.transpose * M).trace

omit [DecidableEq ι] in
/-- Entrywise expression for the squared Frobenius norm. -/
theorem frobeniusSq_eq_sum (M : Matrix ι ι ℝ) :
    frobeniusSq M = ∑ i, ∑ j, (M i j) ^ 2 := by
  simp only [frobeniusSq, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply, sq]
  rw [Finset.sum_comm]

/-- Independent orthogonal changes of row and column bases preserve the Frobenius norm. -/
theorem frobeniusSq_orthogonal (M U V : Matrix ι ι ℝ)
    (hU : U * U.transpose = 1) (hV : V * V.transpose = 1) :
    frobeniusSq (U.transpose * M * V) = frobeniusSq M := by
  unfold frobeniusSq
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    _ = (V.transpose * M.transpose * (U * U.transpose) * M * V).trace := by
      simp only [Matrix.mul_assoc]
    _ = (V.transpose * M.transpose * M * V).trace := by rw [hU, Matrix.mul_one]
    _ = (V * (V.transpose * M.transpose * M)).trace := Matrix.trace_mul_comm _ _
    _ = ((V * V.transpose) * (M.transpose * M)).trace := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hV, Matrix.one_mul]

/-- Entrywise comparison after choosing the two eigenbases. -/
theorem frobeniusSq_diagonal_difference_le (a b : ι → ℝ) (W : Matrix ι ι ℝ)
    (q : ℝ → ℝ) (hq : ∀ x y, |q x - q y| ≤ |x - y|) :
    frobeniusSq (diagonal (q ∘ a) * W - W * diagonal (q ∘ b)) ≤
      frobeniusSq (diagonal a * W - W * diagonal b) := by
  rw [frobeniusSq_eq_sum, frobeniusSq_eq_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.mul_diagonal]
  have hab : (q (a i) - q (b j)) ^ 2 ≤ (a i - b j) ^ 2 := by
    exact (sq_le_sq).2 (hq (a i) (b j))
  have hw := mul_le_mul_of_nonneg_right hab (sq_nonneg (W i j))
  dsimp only [Function.comp_apply]
  nlinarith

/-- A scalar contraction acts as a contraction on Hermitian matrices for the Frobenius norm. -/
theorem cfc_frobeniusSq_le {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (q : ℝ → ℝ) (hq : ∀ x y, |q x - q y| ≤ |x - y|) :
    frobeniusSq (cfc q A - cfc q B) ≤ frobeniusSq (A - B) := by
  let U : Matrix ι ι ℝ := hA.eigenvectorUnitary
  let V : Matrix ι ι ℝ := hB.eigenvectorUnitary
  have hUU : U * U.transpose = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hVV : V * V.transpose = 1 := by
    simpa [V, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hB.eigenvectorUnitary
  have hUtU : U.transpose * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hVtV : V.transpose * V = 1 := by
    simpa [V, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hB.eigenvectorUnitary
  have ha : A = U * diagonal hA.eigenvalues * U.transpose := by
    simpa [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def] using hA.spectral_theorem
  have hb : B = V * diagonal hB.eigenvalues * V.transpose := by
    simpa [V, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def] using hB.spectral_theorem
  have hqa : cfc q A = U * diagonal (q ∘ hA.eigenvalues) * U.transpose := by
    rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    simp [U, Matrix.star_eq_conjTranspose, Function.comp_def]
  have hqb : cfc q B = V * diagonal (q ∘ hB.eigenvalues) * V.transpose := by
    rw [hB.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    simp [V, Matrix.star_eq_conjTranspose, Function.comp_def]
  have hcross (D E : Matrix ι ι ℝ) :
      U.transpose * (U * D * U.transpose - V * E * V.transpose) * V =
        D * (U.transpose * V) - (U.transpose * V) * E := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    calc
      _ = (U.transpose * U) * D * (U.transpose * V) -
          (U.transpose * V) * E * (V.transpose * V) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUtU, hVtV, Matrix.one_mul, Matrix.mul_one]
  have hdiff : U.transpose * (A - B) * V =
      diagonal hA.eigenvalues * (U.transpose * V) -
        (U.transpose * V) * diagonal hB.eigenvalues := by
    calc
      _ = U.transpose * (U * diagonal hA.eigenvalues * U.transpose -
          V * diagonal hB.eigenvalues * V.transpose) * V :=
        congrArg (fun M => U.transpose * M * V) (congrArg₂ (· - ·) ha hb)
      _ = _ := hcross _ _
  rw [← frobeniusSq_orthogonal (cfc q A - cfc q B) U V hUU hVV,
    ← frobeniusSq_orthogonal (A - B) U V hUU hVV, hqa, hqb, hdiff, hcross]
  exact frobeniusSq_diagonal_difference_le hA.eigenvalues hB.eigenvalues
    (U.transpose * V) q hq

/-- Entry-square formulation of the Frobenius spectral contraction, as used in Section 6. -/
theorem cfc_entry_square_sum_le {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (q : ℝ → ℝ) (hq : ∀ x y, |q x - q y| ≤ |x - y|) :
    (∑ i, ∑ j, (cfc q A i j - cfc q B i j) ^ 2) ≤
      ∑ i, ∑ j, (A i j - B i j) ^ 2 := by
  simpa only [frobeniusSq_eq_sum, Matrix.sub_apply] using cfc_frobeniusSq_le hA hB q hq

end Submission.Obl.Entropy__equality_cases
