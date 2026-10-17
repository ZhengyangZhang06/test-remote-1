import Submission.Obl.Entropy__equality_cases.Rigidity

namespace Submission.Obl.Entropy__equality_cases

open Matrix

/-- Simultaneous orthogonal diagonalization of the coefficient matrices. -/
theorem simultaneous_diagonalization {m : ℕ} (X : Fin m → Matrix (Fin m) (Fin m) ℝ)
    (hX : ∀ r, (X r).IsHermitian) (hcomm : ∀ r s, Commute (X r) (X s)) :
    ∃ U : Matrix (Fin m) (Fin m) ℝ,
      U * U.transpose = 1 ∧ U.transpose * U = 1 ∧
      ∃ eig : Fin m → Fin m → ℝ,
        ∀ r, U.transpose * X r * U = diagonal (eig r) := by
  obtain ⟨b, eig, heig⟩ := matrix_joint_orthonormalBasis X hX hcomm
  let e := EuclideanSpace.basisFun (Fin m) ℝ
  let U := e.toBasis.toMatrix b
  have hU : ∀ i j, U i j = b j i := by
    intro i j
    simp [U, e, Module.Basis.toMatrix_apply]
  have hUU : U * U.transpose = 1 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      e.toMatrix_orthonormalBasis_self_mul_conjTranspose b
  have hUtU : U.transpose * U = 1 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      e.toMatrix_orthonormalBasis_conjTranspose_mul_self b
  refine ⟨U, hUU, hUtU, eig, ?_⟩
  intro r
  have hXU : X r * U = U * diagonal (eig r) := by
    ext i j
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin m) => v i) (heig r j)
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [hU]
    simpa only [Matrix.toLpLin_apply, PiLp.smul_apply, Matrix.mulVec, dotProduct,
      smul_eq_mul, mul_comm] using h
  rw [Matrix.mul_assoc, hXU, ← Matrix.mul_assoc, hUtU, Matrix.one_mul]

end Submission.Obl.Entropy__equality_cases
