/-
Adapted from: here:root

Coordinate moment identities written in session x0003 for the cone reduction.
-/

import Mathlib
import ChallengeDeps
import Submission.Lib.ConvexBody

open SimplexIsotropic MeasureTheory

namespace Submission.Lib.BodyMoments

/-- Coordinate projections commute with the defining integral of the centroid. -/
theorem centroid_coordinate {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (i : Fin n) :
    centroid K i = (vol K)⁻¹ * ∫ x in K, x i := by
  have hint : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) => x) K :=
    ContinuousOn.integrableOn_compact hK continuous_id.continuousOn
  have heq := (EuclideanSpace.proj i).integral_comp_comm hint
  change (∫ x in K, x i) = (∫ x in K, x) i at heq
  simp only [centroid, PiLp.smul_apply, smul_eq_mul, heq]

/-- The first coordinate moments of a body's uniform measure. -/
theorem body_first_moment {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsConvexBody K) (i : Fin n) :
    (∫ x in K, x i) = vol K * centroid K i := by
  rw [centroid_coordinate hK.isCompact]
  field_simp [ne_of_gt (Submission.Lib.ConvexBody.body_vol_pos hK)]

/-- The centered coordinates have zero integral over a convex body. -/
theorem body_centered_first_moment {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsConvexBody K) (i : Fin n) :
    (∫ x in K, (x i - centroid K i)) = 0 := by
  have hi : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) => x i) K :=
    ContinuousOn.integrableOn_compact hK.isCompact (by fun_prop)
  have hb : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => centroid K i) K :=
    ContinuousOn.integrableOn_compact hK.isCompact continuousOn_const
  rw [integral_sub hi hb, body_first_moment hK]
  simp [integral_const, vol]

/-- Covariance is the raw second moment minus the product of the first moments. -/
theorem body_covMatrix_raw_moment {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsConvexBody K) (i j : Fin n) :
    covMatrix K i j = (vol K)⁻¹ * (∫ x in K, x i * x j) - centroid K i * centroid K j := by
  have hi : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) => x i * x j) K :=
    ContinuousOn.integrableOn_compact hK.isCompact (by fun_prop)
  have hij : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) => x i * centroid K j) K :=
    ContinuousOn.integrableOn_compact hK.isCompact (by fun_prop)
  have hji : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) => centroid K i * x j) K :=
    ContinuousOn.integrableOn_compact hK.isCompact (by fun_prop)
  have hb : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => centroid K i * centroid K j) K :=
    ContinuousOn.integrableOn_compact hK.isCompact continuousOn_const
  have hiSub : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
      x i * x j - x i * centroid K j) K := hi.sub hij
  have hiSubSub : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
      x i * x j - x i * centroid K j - centroid K i * x j) K := hiSub.sub hji
  unfold covMatrix
  rw [show (fun x : EuclideanSpace ℝ (Fin n) =>
      (x i - centroid K i) * (x j - centroid K j)) =
      (fun x => (x i * x j - x i * centroid K j) - centroid K i * x j +
        centroid K i * centroid K j) by funext x; ring]
  rw [integral_add hiSubSub hb,
    integral_sub hiSub hji, integral_sub hi hij,
    integral_mul_const, integral_const_mul, body_first_moment hK, body_first_moment hK]
  simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
  change (vol K)⁻¹ * ((_ - vol K * centroid K i * centroid K j) -
    centroid K i * (vol K * centroid K j) + vol K * (centroid K i * centroid K j)) = _
  field_simp [ne_of_gt (Submission.Lib.ConvexBody.body_vol_pos hK)]
  ring

end Submission.Lib.BodyMoments
