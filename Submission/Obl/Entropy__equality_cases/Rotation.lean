import Submission.Obl.Entropy__equality_cases.Rigidity

namespace Submission.Obl.Entropy__equality_cases

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Change the coordinates of both the domain and the range of a linear matrix field. -/
def rotatedCoefficients (X : ι → Matrix ι ι ℝ) (U : Matrix ι ι ℝ) (r : ι) :
    Matrix ι ι ℝ :=
  U.transpose * linearField X (fun s => U s r) * U

omit [DecidableEq ι] in
/-- Symmetry of the coefficient tensor is invariant under a change of variables. -/
theorem rotatedCoefficients_symmetry (X : ι → Matrix ι ι ℝ)
    (hX : CoefficientSymmetry X) (U : Matrix ι ι ℝ) :
    CoefficientSymmetry (rotatedCoefficients X U) := by
  intro r s i
  have h := congrFun (congrArg (fun v => U.transpose *ᵥ v)
    (linearField_mulVec_comm X hX (fun k => U k r) (fun k => U k s))) i
  change (U.transpose * linearField X (fun k => U k r) * U) i s =
    (U.transpose * linearField X (fun k => U k s) * U) i r
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h

/-- Mixing a family by an orthogonal matrix preserves its sum of squares. -/
theorem linearField_sum_square (X : ι → Matrix ι ι ℝ) (U : Matrix ι ι ℝ)
    (hU : U * U.transpose = 1) :
    ∑ r, linearField X (fun s => U s r) * linearField X (fun s => U s r) =
      ∑ r, X r * X r := by
  have hu : ∀ s t, ∑ r, U s r * U t r = if s = t then 1 else 0 := by
    intro s t
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      congrArg (fun M : Matrix ι ι ℝ => M s t) hU
  simp only [linearField, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hu]
  simp

/-- Orthogonal rotation preserves the normalization on coefficient squares. -/
theorem rotatedCoefficients_sum_square (X : ι → Matrix ι ι ℝ) (U : Matrix ι ι ℝ)
    (hUU : U * U.transpose = 1) (hUtU : U.transpose * U = 1)
    (hX : ∑ r, X r * X r = 1) :
    ∑ r, rotatedCoefficients X U r * rotatedCoefficients X U r = 1 := by
  have h (M : Matrix ι ι ℝ) :
      (U.transpose * M * U) * (U.transpose * M * U) =
        U.transpose * (M * M) * U := by
    calc
      _ = U.transpose * M * (U * U.transpose) * M * U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  simp only [rotatedCoefficients, h]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, linearField_sum_square X U hUU, hX]
  simpa using hUtU

end Submission.Obl.Entropy__equality_cases
