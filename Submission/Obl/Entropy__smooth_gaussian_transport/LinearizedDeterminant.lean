import Submission.Obl.Entropy__smooth_gaussian_transport.DeterminantConcavity

open scoped RealInnerProductSpace MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- The differential of the log determinant at an invertible Hessian. -/
noncomputable def linearizedTrace {m : ℕ} (A B : E m →L[ℝ] E m) : ℝ :=
  Matrix.trace ((operatorMatrix A)⁻¹ * operatorMatrix B)

theorem linearizedTrace_add {m : ℕ} (A B C : E m →L[ℝ] E m) :
    linearizedTrace A (B + C) = linearizedTrace A B + linearizedTrace A C := by
  simp only [linearizedTrace, operatorMatrix, ContinuousLinearMap.toLinearMap_add,
    map_add, Matrix.mul_add, Matrix.trace_add]

theorem linearizedTrace_sub {m : ℕ} (A B C : E m →L[ℝ] E m) :
    linearizedTrace A (B - C) = linearizedTrace A B - linearizedTrace A C := by
  simp only [linearizedTrace, operatorMatrix, ContinuousLinearMap.toLinearMap_sub,
    map_sub, Matrix.mul_sub, Matrix.trace_sub]

theorem linearizedTrace_smul {m : ℕ} (A B : E m →L[ℝ] E m) (c : ℝ) :
    linearizedTrace A (c • B) = c * linearizedTrace A B := by
  simp only [linearizedTrace, operatorMatrix, ContinuousLinearMap.toLinearMap_smul,
    map_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

theorem linearizedTrace_self {m : ℕ} {A : E m →L[ℝ] E m}
    (hA : (operatorMatrix A).PosDef) : linearizedTrace A A = m := by
  rw [linearizedTrace, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne')]
  simp

/-- The supporting plane inequality, written for the difference of Hessians. -/
theorem log_det_sub_le_linearizedTrace {m : ℕ} {A B : E m →L[ℝ] E m}
    (hA : (operatorMatrix A).PosDef) (hB : (operatorMatrix B).PosDef) :
    Real.log B.det - Real.log A.det ≤ linearizedTrace A (B - A) := by
  have hs := Submission.Lib.EntropyRemainder.log_det_supporting_plane hB hA.inv
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Real.log_inv,
    operatorMatrix_det, operatorMatrix_det] at hs
  rw [linearizedTrace_sub, linearizedTrace_self hA]
  change Real.log B.det - Real.log A.det ≤
    Matrix.trace ((operatorMatrix A)⁻¹ * operatorMatrix B) - (m : ℝ)
  linarith

theorem log_det_midpoint_sub_le_linearizedTrace {m : ℕ}
    {A B C : E m →L[ℝ] E m}
    (hA : (operatorMatrix A).PosDef) (hB : (operatorMatrix B).PosDef)
    (hC : (operatorMatrix C).PosDef) :
    (Real.log B.det + Real.log C.det) / 2 - Real.log A.det ≤
      linearizedTrace A ((1 / 2 : ℝ) • (B + C) - A) := by
  have h₁ := log_det_sub_le_linearizedTrace hA hB
  have h₂ := log_det_sub_le_linearizedTrace hA hC
  simp only [linearizedTrace_sub, linearizedTrace_smul, linearizedTrace_add] at *
  linarith

/-- Positive semidefinite increments have nonnegative linearized trace. -/
theorem linearizedTrace_nonneg {m : ℕ} {A B : E m →L[ℝ] E m}
    (hA : (operatorMatrix A).PosDef) (hB : (operatorMatrix B).PosSemidef) :
    0 ≤ linearizedTrace A B := by
  let S := (operatorMatrix A)⁻¹
  let R := CFC.sqrt S
  have hR : R.IsHermitian := (CFC.sqrt_nonneg S).isSelfAdjoint
  have hRR : R * R = S := CFC.sqrt_mul_sqrt_self S hA.inv.posSemidef.nonneg
  have hpos : (R * operatorMatrix B * R).PosSemidef := by
    simpa only [hR.eq] using hB.conjTranspose_mul_mul_same R
  have htrace : Matrix.trace (R * operatorMatrix B * R) = linearizedTrace A B := by
    rw [Matrix.trace_mul_cycle, hRR]
    rfl
  rw [← htrace]
  exact hpos.trace_nonneg

end Submission.Obl.Entropy__smooth_gaussian_transport
