import Mathlib
import ChallengeDeps
import Submission.Lib.BodyMoments

open SimplexIsotropic MeasureTheory

namespace Submission.Obl.Root

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

end Submission.Obl.Root
