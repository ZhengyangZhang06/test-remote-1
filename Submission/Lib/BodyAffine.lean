/-
Adapted from: here:root

Affine invariance and centroid-zero reduction for convex bodies, following the
introduction and Section 7 of the supplied paper. Written in session x0013.
-/

import Mathlib
import ChallengeDeps
import Submission.Lib.BodyMoments

open SimplexIsotropic MeasureTheory

namespace Submission.Lib.BodyAffine

/-- The class of convex bodies is preserved by invertible affine transformations. -/
theorem body_affine_image {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsConvexBody K)
    (e : EuclideanSpace ℝ (Fin n) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin n)) :
    IsConvexBody (e '' K) := by
  let h := e.toContinuousAffineEquiv.toHomeomorph
  refine ⟨hK.convex.affine_image e.toAffineMap, hK.isCompact.image h.continuous, ?_⟩
  change (interior (h '' K)).Nonempty
  rw [← h.image_interior]
  exact hK.interior_nonempty.image h

/-- Invertible affine transformations preserve the frozen notion of simplex. -/
theorem simplex_affine_image {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsSimplex K)
    (e : EuclideanSpace ℝ (Fin n) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin n)) :
    IsSimplex (e '' K) := by
  rcases hK with ⟨v, hv, rfl⟩
  refine ⟨e ∘ v, e.affineIndependent_iff.mpr hv, ?_⟩
  simpa only [Set.range_comp, AffineEquiv.coe_coe] using e.toAffineMap.image_convexHull (Set.range v)

/-- Being a simplex is invariant under invertible affine changes of coordinates. -/
theorem simplex_affine_image_iff {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (e : EuclideanSpace ℝ (Fin n) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin n)) :
    IsSimplex (e '' K) ↔ IsSimplex K := by
  refine ⟨fun h => ?_, fun h => simplex_affine_image h e⟩
  have h' := simplex_affine_image h e.symm
  simpa [Set.image_image] using h'

/-- Translation does not change the volume of a set. -/
theorem vol_translate {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) :
    vol ((fun x => a + x) '' K) = vol K := by
  have h := (measurePreserving_add_left volume a).setIntegral_image_emb
    (MeasurableEquiv.addLeft a).measurableEmbedding (fun _ => (1 : ℝ)) K
  simpa [integral_const, vol] using h

/-- Change of variables for translation, valid for the total Bochner integral. -/
theorem integral_translate {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Set (EuclideanSpace ℝ (Fin n))) (a : EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → F) :
    (∫ x in (fun x => a + x) '' K, f x) = ∫ x in K, f (a + x) :=
  (measurePreserving_add_left volume a).setIntegral_image_emb
    (MeasurableEquiv.addLeft a).measurableEmbedding f K

/-- The centroid follows translations of a convex body. -/
theorem centroid_translate {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsConvexBody K) (a : EuclideanSpace ℝ (Fin n)) :
    centroid ((fun x => a + x) '' K) = a + centroid K := by
  have hi : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) => x) K :=
    ContinuousOn.integrableOn_compact hK.isCompact continuous_id.continuousOn
  have ha : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => a) K :=
    ContinuousOn.integrableOn_compact hK.isCompact continuousOn_const
  rw [centroid, vol_translate, integral_translate, integral_add ha hi]
  simp only [integral_const, measureReal_restrict_apply_univ, smul_add, smul_smul]
  rw [show (volume.real K) = vol K from rfl,
    inv_mul_cancel₀ (ne_of_gt (Submission.Lib.ConvexBody.body_vol_pos hK)), one_smul]
  rfl

/-- Centered covariance is unchanged by translation. -/
theorem covMatrix_translate {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsConvexBody K) (a : EuclideanSpace ℝ (Fin n)) :
    covMatrix ((fun x => a + x) '' K) = covMatrix K := by
  ext i j
  simp only [covMatrix, vol_translate, centroid_translate hK, integral_translate,
    PiLp.add_apply, add_sub_add_left_eq_sub]

/-- The isotropic constant is translation invariant. -/
theorem isotropicConstant_translate {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsConvexBody K) (a : EuclideanSpace ℝ (Fin n)) :
    isotropicConstant ((fun x => a + x) '' K) = isotropicConstant K := by
  simp only [isotropicConstant, covMatrix_translate hK, vol_translate]

/-- The centroid-zero reduction used at the start of Section 7. -/
theorem exists_centered_body {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsConvexBody K) :
    ∃ K₀ : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K₀ ∧ centroid K₀ = 0 ∧
      vol K₀ = vol K ∧ covMatrix K₀ = covMatrix K ∧
      isotropicConstant K₀ = isotropicConstant K ∧ (IsSimplex K₀ ↔ IsSimplex K) := by
  let a := -centroid K
  let e := AffineEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin n)) a
  refine ⟨e '' K, body_affine_image hK e, ?_, vol_translate K a,
    covMatrix_translate hK a, isotropicConstant_translate hK a,
    simplex_affine_image_iff K e⟩
  change centroid ((fun x => a + x) '' K) = 0
  rw [centroid_translate hK]
  exact neg_add_cancel _



/-- Linear change of variables for the Euclidean volume used in the challenge. -/
theorem vol_linear_image {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    vol (e '' K) = |LinearMap.det e.toLinearMap| * vol K := by
  unfold vol Measure.real
  rw [volume.addHaar_image_continuousLinearEquiv e K, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]

/-- The set-integral substitution formula for an invertible linear transformation. -/
theorem integral_linear_image {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → F) :
    (∫ x in e '' K, f x) =
      |LinearMap.det e.toLinearMap| • ∫ x in K, f (e x) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hK
    (fun x _ => e.hasFDerivAt.hasFDerivWithinAt) e.injective.injOn]
  exact integral_smul _ _

/-- Centroids commute with invertible linear maps. -/
theorem centroid_linear_image {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    centroid (e '' K) = e (centroid K) := by
  have hd : |LinearMap.det e.toLinearMap| ≠ 0 :=
    abs_ne_zero.mpr e.toLinearEquiv.isUnit_det'.ne_zero
  rw [centroid, vol_linear_image, integral_linear_image hK,
    e.integral_comp_comm (fun x => x)]
  simp only [mul_inv_rev, smul_smul, mul_assoc, inv_mul_cancel₀ hd, mul_one]
  exact (e.map_smul _ _).symm

/-- The matrix of a Euclidean linear map in the coordinate orthonormal basis. -/
noncomputable def euclideanMatrix {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis e

/-- The coordinate formula associated with `euclideanMatrix`. -/
theorem euclideanMatrix_apply {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    e x i = ∑ j, euclideanMatrix e i j * x j := by
  have h := congrFun (LinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis e x) i
  simpa [euclideanMatrix, Matrix.mulVec, dotProduct,
    OrthonormalBasis.coe_toBasis_repr_apply] using h.symm

/-- Matrix determinants agree with the intrinsic determinant of the linear map. -/
theorem euclideanMatrix_det {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (euclideanMatrix e).det = LinearMap.det e :=
  LinearMap.det_toMatrix _ _

/-- Normalization by volume cancels the Jacobian in a linear substitution. -/
theorem normalized_integral_linear_image {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (vol (e '' K))⁻¹ * (∫ x in e '' K, f x) =
      (vol K)⁻¹ * ∫ x in K, f (e x) := by
  have hd : |LinearMap.det e.toLinearMap| ≠ 0 :=
    abs_ne_zero.mpr e.toLinearEquiv.isUnit_det'.ne_zero
  rw [vol_linear_image, integral_linear_image hK]
  simp only [smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left₀ hd]

/-- Covariance transforms by matrix congruence under an invertible linear map. -/
theorem covMatrix_linear_image {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    covMatrix (e '' K) = euclideanMatrix e.toLinearMap * covMatrix K *
      (euclideanMatrix e.toLinearMap).transpose := by
  let M := euclideanMatrix e.toLinearMap
  have hc (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
      e x i - e (centroid K) i = ∑ k, M i k * (x k - centroid K k) := by
    change e.toLinearMap x i - e.toLinearMap (centroid K) i = _
    rw [euclideanMatrix_apply, euclideanMatrix_apply]
    simp only [M, mul_sub, Finset.sum_sub_distrib]
  ext i j
  change (vol (e '' K))⁻¹ * (∫ x in e '' K,
    (x i - centroid (e '' K) i) * (x j - centroid (e '' K) j)) = _
  rw [normalized_integral_linear_image hK.measurableSet e,
    centroid_linear_image hK.measurableSet]
  have hf : (fun x : EuclideanSpace ℝ (Fin n) =>
      (e x i - e (centroid K) i) * (e x j - e (centroid K) j)) =
      (fun x => ∑ k, ∑ l, (M i k * M j l) *
        ((x k - centroid K k) * (x l - centroid K l))) := by
    funext x
    rw [hc, hc]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hi (k l : Fin n) : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
      (M i k * M j l) * ((x k - centroid K k) * (x l - centroid K l))) K :=
    ContinuousOn.integrableOn_compact hK (by fun_prop)
  rw [hf, integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hi k l))]
  simp_rw [integral_finsetSum _ (fun l _ => hi _ l), integral_const_mul]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, covMatrix,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  dsimp [M]
  ring

/-- The covariance determinant gains the square of the linear determinant. -/
theorem covMatrix_det_linear_image {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (covMatrix (e '' K)).det = (LinearMap.det e.toLinearMap) ^ 2 * (covMatrix K).det := by
  rw [covMatrix_linear_image hK, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, euclideanMatrix_det]
  ring

/-- The isotropic constant is invariant under invertible linear maps. -/
theorem isotropicConstant_linear_image {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    isotropicConstant (e '' K) = isotropicConstant K := by
  have hd : LinearMap.det e.toLinearMap ≠ 0 := e.toLinearEquiv.isUnit_det'.ne_zero
  unfold isotropicConstant
  rw [covMatrix_det_linear_image hK, vol_linear_image, mul_pow, sq_abs,
    mul_div_mul_left _ _ (pow_ne_zero _ hd)]

/-- Decompose an affine map into its translation and linear parts. -/
theorem affine_apply_eq {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : e x = e 0 + e.linear x := by
  simpa only [vadd_eq_add, add_zero, add_comm] using e.map_vadd 0 x

/-- Set-level form of the affine decomposition. -/
theorem affine_image_eq {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (e : EuclideanSpace ℝ (Fin n) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin n)) :
    e '' K = (fun x => e 0 + x) '' (e.linear.toContinuousLinearEquiv '' K) := by
  rw [Set.image_image]
  congr 1
  funext x
  exact affine_apply_eq e x

/-- Euclidean volume gains the absolute linear determinant under an affine map. -/
theorem vol_affine_image {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (e : EuclideanSpace ℝ (Fin n) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin n)) :
    vol (e '' K) = |LinearMap.det e.linear.toLinearMap| * vol K := by
  rw [affine_image_eq, vol_translate, vol_linear_image]
  rfl

/-- Centroids commute with invertible affine maps. -/
theorem centroid_affine_image {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsConvexBody K)
    (e : EuclideanSpace ℝ (Fin n) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin n)) :
    centroid (e '' K) = e (centroid K) := by
  have hL : IsConvexBody (e.linear.toContinuousLinearEquiv '' K) :=
    body_affine_image hK e.linear.toAffineEquiv
  rw [affine_image_eq, centroid_translate hL,
    centroid_linear_image hK.isCompact.measurableSet, affine_apply_eq e (centroid K)]
  rfl

/-- Affine translations disappear from the covariance transformation law. -/
theorem covMatrix_affine_image {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsConvexBody K)
    (e : EuclideanSpace ℝ (Fin n) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin n)) :
    covMatrix (e '' K) = euclideanMatrix e.linear.toLinearMap * covMatrix K *
      (euclideanMatrix e.linear.toLinearMap).transpose := by
  have hL : IsConvexBody (e.linear.toContinuousLinearEquiv '' K) :=
    body_affine_image hK e.linear.toAffineEquiv
  rw [affine_image_eq, covMatrix_translate hL, covMatrix_linear_image hK.isCompact]
  rfl

/-- Covariance determinant formula for an invertible affine change of coordinates. -/
theorem covMatrix_det_affine_image {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsConvexBody K)
    (e : EuclideanSpace ℝ (Fin n) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (covMatrix (e '' K)).det = (LinearMap.det e.linear.toLinearMap) ^ 2 * (covMatrix K).det := by
  rw [covMatrix_affine_image hK, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, euclideanMatrix_det]
  ring

/-- The affine invariance asserted in the introduction of the supplied paper. -/
theorem isotropicConstant_affine_image {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsConvexBody K)
    (e : EuclideanSpace ℝ (Fin n) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin n)) :
    isotropicConstant (e '' K) = isotropicConstant K := by
  have hL : IsConvexBody (e.linear.toContinuousLinearEquiv '' K) :=
    body_affine_image hK e.linear.toAffineEquiv
  rw [affine_image_eq, isotropicConstant_translate hL,
    isotropicConstant_linear_image hK.isCompact]

end Submission.Lib.BodyAffine
