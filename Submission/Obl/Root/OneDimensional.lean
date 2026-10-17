import Submission.Obl.Root.Algebra
import Submission.Obl.Root.Normalization

open SimplexIsotropic MeasureTheory Set

namespace Submission.Obl.Root

/-- The coordinate equivalence between the one-dimensional Euclidean model and the real line. -/
noncomputable def lineCoord : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  (EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)

@[simp] theorem lineCoord_apply (x : EuclideanSpace ℝ (Fin 1)) : lineCoord x = x 0 := rfl

@[simp] theorem lineCoord_symm_apply (x : ℝ) (i : Fin 1) : lineCoord.symm x i = x := by
  fin_cases i
  rfl

theorem lineCoord_measurePreserving : MeasurePreserving lineCoord :=
  (volume_preserving_funUnique (Fin 1) ℝ).comp (PiLp.volume_preserving_ofLp (Fin 1))

theorem lineCoord_symm_measurePreserving : MeasurePreserving lineCoord.symm :=
  lineCoord_measurePreserving.symm lineCoord.toHomeomorph.toMeasurableEquiv

/-- A closed interval represented in the Euclidean model of the challenge. -/
noncomputable def lineInterval (a b : ℝ) : Set (EuclideanSpace ℝ (Fin 1)) :=
  lineCoord.symm '' Icc a b

theorem lineInterval_body {a b : ℝ} (hab : a < b) : IsConvexBody (lineInterval a b) := by
  refine ⟨(convex_Icc a b).linear_image lineCoord.symm.toLinearMap,
    isCompact_Icc.image lineCoord.symm.continuous, ?_⟩
  change (interior (lineCoord.symm.toHomeomorph '' Icc a b)).Nonempty
  rw [← lineCoord.symm.toHomeomorph.image_interior, interior_Icc]
  exact (nonempty_Ioo.mpr hab).image _

/-- Every one-dimensional convex body is a nondegenerate interval. -/
theorem body_one_eq_interval {K : Set (EuclideanSpace ℝ (Fin 1))}
    (hK : IsConvexBody K) : ∃ a b : ℝ, a < b ∧ K = lineInterval a b := by
  let S := lineCoord '' K
  have hS : IsCompact S := hK.isCompact.image lineCoord.continuous
  have hconv : Convex ℝ S := hK.convex.linear_image lineCoord.toLinearMap
  have hne : S.Nonempty := (hK.interior_nonempty.mono interior_subset).image _
  have heq := eq_Icc_of_connected_compact (hconv.isConnected hne) hS
  have hi : (interior S).Nonempty := by
    change (interior (lineCoord.toHomeomorph '' K)).Nonempty
    rw [← lineCoord.toHomeomorph.image_interior]
    exact hK.interior_nonempty.image _
  rw [heq, interior_Icc, nonempty_Ioo] at hi
  refine ⟨sInf S, sSup S, hi, ?_⟩
  unfold lineInterval
  rw [← heq]
  simp only [S, Set.image_image,
    ContinuousLinearEquiv.symm_apply_apply, Set.image_id']

/-- In dimension one every convex body is a simplex. -/
theorem body_one_simplex {K : Set (EuclideanSpace ℝ (Fin 1))}
    (hK : IsConvexBody K) : IsSimplex K := by
  obtain ⟨a, b, hab, rfl⟩ := body_one_eq_interval hK
  refine ⟨![lineCoord.symm a, lineCoord.symm b],
    affineIndependent_of_ne ℝ (fun h => hab.ne (lineCoord.symm.injective h)), ?_⟩
  rw [Matrix.range_cons_cons_empty, convexHull_pair]
  unfold lineInterval
  rw [← segment_eq_Icc hab.le, ← convexHull_pair, ← convexHull_pair]
  change lineCoord.symm.toLinearMap '' convexHull ℝ ({a, b} : Set ℝ) =
    convexHull ℝ {lineCoord.symm.toLinearMap a, lineCoord.symm.toLinearMap b}
  rw [LinearMap.image_convexHull, Set.image_pair]

/-- Integration over a Euclidean line interval is ordinary real interval integration. -/
theorem integral_lineInterval {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a b : ℝ) (f : EuclideanSpace ℝ (Fin 1) → F) :
    (∫ x in lineInterval a b, f x) = ∫ t in Icc a b, f (lineCoord.symm t) :=
  lineCoord_symm_measurePreserving.setIntegral_image_emb
    lineCoord.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding f _

/-- Length agrees with the frozen Euclidean volume convention. -/
theorem vol_lineInterval {a b : ℝ} (hab : a ≤ b) : vol (lineInterval a b) = b - a := by
  have h := integral_lineInterval a b (fun _ => (1 : ℝ))
  simpa [integral_const, vol, Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using h

/-- The centroid of an interval is its midpoint. -/
theorem centroid_lineInterval {a b : ℝ} (hab : a < b) :
    centroid (lineInterval a b) 0 = (a + b) / 2 := by
  rw [Submission.Lib.BodyMoments.centroid_coordinate (lineInterval_body hab).isCompact,
    vol_lineInterval hab.le, integral_lineInterval]
  simp only [lineCoord_symm_apply]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le,
    integral_id]
  field_simp [sub_ne_zero.mpr hab.ne']
  ring

/-- The variance of a uniform interval is its squared length divided by twelve. -/
theorem covMatrix_lineInterval {a b : ℝ} (hab : a < b) :
    covMatrix (lineInterval a b) 0 0 = (b - a) ^ 2 / 12 := by
  rw [Submission.Lib.BodyMoments.body_covMatrix_raw_moment (lineInterval_body hab),
    centroid_lineInterval hab, vol_lineInterval hab.le, integral_lineInterval]
  simp only [lineCoord_symm_apply]
  simp_rw [← pow_two]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le, integral_pow]
  norm_num
  field_simp [sub_ne_zero.mpr hab.ne']
  ring

/-- The simplex determinant identity holds for every one-dimensional convex body. -/
theorem body_one_det_identity {K : Set (EuclideanSpace ℝ (Fin 1))}
    (hK : IsConvexBody K) : 12 * (covMatrix K).det = vol K ^ 2 := by
  obtain ⟨a, b, hab, rfl⟩ := body_one_eq_interval hK
  rw [Matrix.det_fin_one, covMatrix_lineInterval hab, vol_lineInterval hab.le]
  ring

/-- The one-dimensional case of the sharp isotropic constant formula. -/
theorem isotropicConstant_one {K : Set (EuclideanSpace ℝ (Fin 1))}
    (hK : IsConvexBody K) : isotropicConstant K = simplexBound 1 := by
  apply (isotropicConstant_eq_iff_det_eq 1 (by omega) K
    (Submission.Lib.ConvexBody.body_vol_pos hK)
    (Submission.Lib.ConvexBody.covMatrix_det_nonneg hK.isCompact)).mpr
  norm_num
  simpa only [Matrix.det_fin_one] using body_one_det_identity hK

/-- Both conclusions of the challenge in dimension one. -/
theorem simplex_inequality_one {K : Set (EuclideanSpace ℝ (Fin 1))}
    (hK : IsConvexBody K) : isotropicConstant K ≤ simplexBound 1 ∧
      (isotropicConstant K = simplexBound 1 ↔ IsSimplex K) :=
  ⟨(isotropicConstant_one hK).le, iff_of_true (isotropicConstant_one hK) (body_one_simplex hK)⟩

end Submission.Obl.Root
