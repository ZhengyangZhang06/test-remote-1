import Submission.Lib.MatrixEntropy.Completion
import Submission.Lib.PairEstimate.MatrixAlgebra

set_option autoImplicit false

open scoped BigOperators MatrixOrder

namespace Submission.Obl.Entropy__transport_finite_jacobian_energy

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma weighted_trace_coercive {P H : Matrix ι ι ℝ} {ε : ℝ}
    (hP : P.PosSemidef) (hε : 0 ≤ ε)
    (hbound : (P - ε • (1 : Matrix ι ι ℝ)).PosSemidef)
    (hH : H.IsHermitian) :
    ε ^ 2 * (∑ i, ∑ j, (H i j) ^ 2) ≤ (P * H * P * H).trace := by
  have hHPH : (H * P * H).PosSemidef := by
    simpa only [hH.eq] using hP.mul_mul_conjTranspose_same H
  have h₁ := Submission.Lib.MatrixEntropy.trace_mul_nonneg_of_posSemidef hbound hHPH
  have h₂ := (hbound.mul_mul_conjTranspose_same H).trace_nonneg
  rw [hH.eq] at h₂
  have hsq : (H * H).trace = ∑ i, ∑ j, (H i j) ^ 2 := by
    have hs : H.transpose = H := by simpa using hH.eq
    rw [← hs]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← congrArg (fun M : Matrix ι ι ℝ => M j i) hs]
    simp only [Matrix.transpose_apply]
    ring
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul,
    smul_eq_mul] at h₁ h₂
  simp only [← Matrix.mul_assoc] at h₁
  rw [hsq] at h₂
  nlinarith [mul_nonneg hε h₂]

end Submission.Obl.Entropy__transport_finite_jacobian_energy
