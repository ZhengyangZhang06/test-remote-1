/-
Adapted from: here:o011

Original proofs by session x0028, shared from the o011 compatibility development.
-/

import Submission.Lib.JacobianCompatibility.PrimitiveCoefficients

/-! The Jacobian compatibility identities of Section 6, Lemma 6.1. -/

namespace Submission.Lib.JacobianCompatibility

open Filter Set
open scoped Topology Matrix.Norms.L2Operator

lemma HasPrimitive.of_smul
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {J : E → E →L[ℝ] V} {c : ℝ} (h : HasPrimitive (fun x ↦ c • J x)) (hc : c ≠ 0) :
    HasPrimitive J := by
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h.smul c⁻¹

/-- A linear Jacobian has symmetric coefficient tensor. -/
theorem linear_compatibility_of_hasPrimitive
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : E →L[ℝ] E →L[ℝ] V) (hB : HasPrimitive B) (v w : E) : B v w = B w v := by
  obtain ⟨f, hf⟩ := hB
  exact second_derivative_symmetric hf (B.hasFDerivAt (x := 0)) v w

/-- Compatibility of the square of a linear field. -/
theorem square_compatibility_of_hasPrimitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] E)
    (hB : HasPrimitive (fun x ↦ (B x).comp (B x))) (x v w : E) :
    B v (B x w) + B x (B v w) = B w (B x v) + B x (B w v) := by
  obtain ⟨f, hf⟩ := hB
  have hd := (B.hasFDerivAt (x := x)).clm_comp (B.hasFDerivAt (x := x))
  have hh := second_derivative_symmetric hf hd v w
  simpa only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply, add_comm] using hh

/-- Extract both matrix compatibility identities from a nonlinear C² Jacobian.
Only its first and second scalar derivatives at zero need to be nonzero. -/
theorem cfc_linear_field_compatibility
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : EuclideanSpace ℝ n →L[ℝ] Matrix n n ℝ) (hA : ∀ x, (A x).IsHermitian)
    {q : ℝ → ℝ} (hqc : ContDiff ℝ 2 q)
    (hq1 : deriv q 0 ≠ 0) (hq2 : deriv (deriv q) 0 ≠ 0)
    (hq : HasPrimitive (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) (cfc q (A x)))) :
    (∀ v w, Matrix.toEuclideanCLM (𝕜 := ℝ) (A v) w =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (A w) v) ∧
    (∀ x v w, Matrix.toEuclideanCLM (𝕜 := ℝ) (A v * A x + A x * A v) w =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (A w * A x + A x * A w) v) := by
  let B : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv
      |>.toContinuousLinearMap.comp A
  have hB : ∀ x, B x = Matrix.toEuclideanCLM (𝕜 := ℝ) (A x) := fun x ↦ rfl
  have hlin : HasPrimitive B := by
    have hp := hasPrimitive_cfc_linear_coefficient A hA
      ((hqc.differentiable (by norm_num)).differentiableAt.hasDerivAt (x := 0)) hq
    have hp' : HasPrimitive (fun x ↦ (2 * deriv q 0) • B x) := by
      simpa only [hB, map_smul] using hp
    exact hp'.of_smul (mul_ne_zero (by norm_num) hq1)
  have hquad : HasPrimitive (fun x ↦ (B x).comp (B x)) := by
    have hp := hasPrimitive_cfc_quadratic_coefficient A hA hqc hq
    have hp' : HasPrimitive (fun x ↦ deriv (deriv q) 0 • (B x).comp (B x)) := by
      simpa only [hB, map_smul, pow_two, map_mul, ContinuousLinearMap.mul_def] using hp
    exact hp'.of_smul hq2
  constructor
  · exact linear_compatibility_of_hasPrimitive B hlin
  · intro x v w
    simpa only [hB, map_add, map_mul, add_apply,
      mul_apply_eq_comp] using square_compatibility_of_hasPrimitive B hquad x v w

end Submission.Lib.JacobianCompatibility
