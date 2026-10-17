import Mathlib

set_option autoImplicit false

open Matrix
open scoped BigOperators Matrix.Norms.Elementwise

namespace Submission.Obl.Entropy__transport_finite_jacobian_energy

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant bundled as a continuous multilinear function of its rows. -/
noncomputable def determinantMultilinear :
    ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
  ⟨Matrix.detRowAlternating.toMultilinearMap, continuous_id.matrix_det⟩

/-- Replacing one row, expressed through the inverse matrix. -/
theorem det_updateRow_eq_trace_term (A B : Matrix ι ι ℝ) (hA : IsUnit A.det) (i : ι) :
    (A.updateRow i (B i)).det = (B * A⁻¹) i i * A.det := by
  have he : B i = ∑ k, (B * A⁻¹) i k • A k := by
    funext j
    simpa [Matrix.mul_apply, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul A hA]
      using (congrArg (fun M : Matrix ι ι ℝ => M i j)
        (show B = B * A⁻¹ * A by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul A hA, Matrix.mul_one]))
  rw [he, Matrix.det_updateRow_sum, smul_eq_mul]

/-- Jacobi's formula for the derivative of the determinant. -/
theorem determinant_linearDeriv_apply (A B : Matrix ι ι ℝ) (hA : IsUnit A.det) :
    (determinantMultilinear (ι := ι)).linearDeriv A B =
      A.det * Matrix.trace (A⁻¹ * B) := by
  erw [ContinuousMultilinearMap.linearDeriv_apply]
  change (∑ i, (A.updateRow i (B i)).det) = _
  simp_rw [det_updateRow_eq_trace_term A B hA]
  rw [← Finset.sum_mul, Matrix.trace_mul_comm A⁻¹ B, Matrix.trace, mul_comm]
  rfl

/-- The log determinant derivative in any differentiable matrix field. -/
theorem fderiv_logdet_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E → Matrix ι ι ℝ} {x : E} (hA : DifferentiableAt ℝ A x)
    (hinv : (A x).det ≠ 0) (v : E) :
    fderiv ℝ (fun y => Real.log (A y).det) x v =
      Matrix.trace ((A x)⁻¹ * fderiv ℝ A x v) := by
  have hd := ((determinantMultilinear (ι := ι)).hasFDerivAt (A x)).comp x hA.hasFDerivAt
  have hl := hd.log hinv
  erw [hl.fderiv]
  change (A x).det⁻¹ * ((determinantMultilinear (ι := ι)).linearDeriv (A x)
    (fderiv ℝ A x v)) = _
  rw [determinant_linearDeriv_apply _ _ (isUnit_iff_ne_zero.mpr hinv)]
  field_simp

/-- Smoothness of the determinant, expressed for matrix fields. -/
theorem contDiff_matrix_det
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E → Matrix ι ι ℝ} {n : WithTop ENat} (hA : ContDiff ℝ n A) :
    ContDiff ℝ n (fun x => (A x).det) :=
  (determinantMultilinear (ι := ι)).contDiff.comp hA

/-- Smoothness of the adjugate follows from its row-replacement formula. -/
theorem contDiff_matrix_adjugate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E → Matrix ι ι ℝ} {n : WithTop ENat} (hA : ContDiff ℝ n A) :
    ContDiff ℝ n (fun x => (A x).adjugate) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp_rw [Matrix.adjugate_apply]
  apply contDiff_matrix_det
  apply contDiff_pi.mpr
  intro r
  apply contDiff_pi.mpr
  intro s
  by_cases h : r = j
  · simpa [Matrix.updateRow, Function.update, h] using
      (contDiff_const : ContDiff ℝ n (fun _ : E => (Pi.single i (1 : ℝ) : ι → ℝ) s))
  · simpa [Matrix.updateRow, Function.update, h] using
      (contDiff_pi.mp (contDiff_pi.mp hA r) s)

/-- An everywhere invertible smooth matrix field has a smooth inverse. -/
theorem contDiff_matrix_inv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E → Matrix ι ι ℝ} {n : WithTop ENat} (hA : ContDiff ℝ n A)
    (hinv : ∀ x, (A x).det ≠ 0) :
    ContDiff ℝ n (fun x => (A x)⁻¹) := by
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Pi.inv_apply] using
    ((contDiff_matrix_det hA).inv hinv).fun_smul (contDiff_matrix_adjugate hA)

end Submission.Obl.Entropy__transport_finite_jacobian_energy
