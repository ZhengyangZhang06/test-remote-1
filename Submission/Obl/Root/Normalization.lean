import Submission.Obl.Root.Linear

open SimplexIsotropic MeasureTheory
open scoped MatrixOrder

namespace Submission.Obl.Root

/-- A positive definite covariance admits an invertible linear normalization to identity. -/
theorem exists_covariance_normalizer {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) :
    ∃ e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      euclideanMatrix e.toLinearMap * A * (euclideanMatrix e.toLinearMap).transpose = 1 := by
  let B := CFC.sqrt A
  have hB : B.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hBu : IsUnit B := (CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).mpr hA.isUnit
  have hsq : B * B = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hd : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hBu
  have hleft : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hd
  have hright : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hd
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let e := (Matrix.toLinOfInv b b hleft hright).toContinuousLinearEquiv
  have hM : euclideanMatrix e.toLinearMap = B⁻¹ := by
    exact LinearMap.toMatrix_toLin b b _
  have hsym : (B⁻¹).transpose = B⁻¹ := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hB.inv.isHermitian
  refine ⟨e, ?_⟩
  rw [hM, hsym, ← hsq, ← mul_assoc, hleft, one_mul, hright]

/-- Every convex body can be put in centered identity-covariance position. -/
theorem exists_isotropic_body {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsConvexBody K) :
    ∃ K₀ : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K₀ ∧ centroid K₀ = 0 ∧
      covMatrix K₀ = 1 ∧ isotropicConstant K₀ = isotropicConstant K ∧
      (IsSimplex K₀ ↔ IsSimplex K) := by
  obtain ⟨Kc, hKc, hc, _, hC, hL, hs⟩ := exists_centered_body hK
  obtain ⟨e, he⟩ := exists_covariance_normalizer (covMatrix Kc)
    (Submission.Lib.ConvexBody.body_covMatrix_posDef hKc)
  refine ⟨e '' Kc, body_affine_image hKc e.toLinearEquiv.toAffineEquiv, ?_, ?_, ?_, ?_⟩
  · rw [centroid_linear_image hKc.isCompact.measurableSet, hc, map_zero]
  · rw [covMatrix_linear_image hKc.isCompact]
    exact he
  · rw [isotropicConstant_linear_image hKc.isCompact, hL]
  · exact (simplex_affine_image_iff Kc e.toLinearEquiv.toAffineEquiv).trans hs

end Submission.Obl.Root
