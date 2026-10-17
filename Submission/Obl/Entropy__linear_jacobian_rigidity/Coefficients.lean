import Submission.Obl.Entropy__linear_jacobian_rigidity.Compatibility

/-! Coordinate form of the two compatibility identities in Lemma 6.1. -/

namespace Submission.Obl.Entropy__linear_jacobian_rigidity

open scoped Topology Matrix.Norms.L2Operator BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The continuous linear matrix field determined by its coefficients. -/
noncomputable def coefficientField (X : n → Matrix n n ℝ) :
    EuclideanSpace ℝ n →L[ℝ] Matrix n n ℝ :=
  ∑ r, (EuclideanSpace.proj r).smulRight (X r)

lemma coefficientField_apply (X : n → Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    coefficientField X x = ∑ r, x r • X r := by
  simp [coefficientField]

lemma coefficientField_single (X : n → Matrix n n ℝ) (r : n) :
    coefficientField X (PiLp.single 2 r 1) = X r := by
  simp [coefficientField_apply, PiLp.single_apply]

lemma coefficientField_isHermitian (X : n → Matrix n n ℝ) (hX : ∀ r, (X r).IsHermitian)
    (x : EuclideanSpace ℝ n) : (coefficientField X x).IsHermitian := by
  rw [coefficientField_apply]
  change (∑ r, x r • X r).conjTranspose = ∑ r, x r • X r
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun r _ ↦ (hX r).smul (isSelfAdjoint_iff.mpr rfl))

/-- The two coefficient identities forced by a nonlinear matrix Jacobian. -/
theorem jacobian_coefficient_identities
    (X : n → Matrix n n ℝ) (hX : ∀ r, (X r).IsHermitian)
    {q : ℝ → ℝ} (hqc : ContDiff ℝ 2 q)
    (hq1 : deriv q 0 ≠ 0) (hq2 : deriv (deriv q) 0 ≠ 0)
    {F : EuclideanSpace ℝ n → EuclideanSpace ℝ n} (hF : Differentiable ℝ F)
    (hJ : ∀ x v i, fderiv ℝ F x v i = ∑ j, cfc q (∑ r, x r • X r) i j * v j) :
    (∀ r s i, X r i s = X s i r) ∧
    (∀ r s t i, (X r * X t + X t * X r) i s = (X s * X t + X t * X s) i r) := by
  have hp : HasPrimitive (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ)
      (cfc q (coefficientField X x))) := by
    refine ⟨F, fun x ↦ ?_⟩
    have heq : fderiv ℝ F x = Matrix.toEuclideanCLM (𝕜 := ℝ)
        (cfc q (coefficientField X x)) := by
      ext v i
      simpa only [coefficientField_apply, Matrix.ofLp_toEuclideanCLM,
        Matrix.mulVec, dotProduct] using hJ x v i
    exact (hF x).hasFDerivAt.congr_fderiv heq
  obtain ⟨hlin, hquad⟩ := cfc_linear_field_compatibility (coefficientField X)
    (coefficientField_isHermitian X hX) hqc hq1 hq2 hp
  constructor
  · intro r s i
    have h := congrArg (fun z : EuclideanSpace ℝ n ↦ z i)
      (hlin (PiLp.single 2 r 1) (PiLp.single 2 s 1))
    simp only [coefficientField_single] at h
    simpa only [PiLp.single, Matrix.toEuclideanCLM_toLp, Matrix.mulVec_single,
      WithLp.ofLp_toLp, MulOpposite.op_one, one_smul, Matrix.col, Matrix.transpose_apply] using h
  · intro r s t i
    have h := congrArg (fun z : EuclideanSpace ℝ n ↦ z i)
      (hquad (PiLp.single 2 t 1) (PiLp.single 2 r 1) (PiLp.single 2 s 1))
    simp only [coefficientField_single] at h
    simpa only [PiLp.single, Matrix.toEuclideanCLM_toLp, Matrix.mulVec_single,
      WithLp.ofLp_toLp, MulOpposite.op_one, one_smul, Matrix.col, Matrix.transpose_apply] using h

end Submission.Obl.Entropy__linear_jacobian_rigidity
