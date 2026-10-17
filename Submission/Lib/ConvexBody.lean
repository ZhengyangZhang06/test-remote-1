/-
Adapted from: here:root

Volume and covariance positivity lemmas written in session x0003 for root.
-/

import Mathlib
import ChallengeDeps

open SimplexIsotropic MeasureTheory
open scoped Matrix

namespace Submission.Lib.ConvexBody

/-- Compact convex bodies have finite, strictly positive Lebesgue volume. -/
theorem body_vol_pos {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsConvexBody K) : 0 < vol K := by
  apply ENNReal.toReal_pos _ hK.isCompact.measure_lt_top.ne
  exact ne_of_gt ((isOpen_interior.measure_pos volume hK.interior_nonempty).trans_le
    (measure_mono interior_subset))

/-- Symmetry of the covariance does not need integrability assumptions. -/
theorem covMatrix_isHermitian {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) :
    (covMatrix K).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, covMatrix]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  exact mul_comm _ _

/-- The quadratic form of the covariance is the integral of a square. -/
theorem covMatrix_quadratic {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (u : Fin n → ℝ) :
    u ⬝ᵥ (covMatrix K *ᵥ u) =
      (vol K)⁻¹ * ∫ x in K, (∑ i, u i * (x i - centroid K i)) ^ 2 := by
  have hc (i : Fin n) : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      u i * (x i - centroid K i)) := by fun_prop
  have hi (i j : Fin n) : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
      (u i * (x i - centroid K i)) * (u j * (x j - centroid K j))) K :=
    ContinuousOn.integrableOn_compact hK ((hc i).mul (hc j)).continuousOn
  rw [show (fun x : EuclideanSpace ℝ (Fin n) => (∑ i, u i * (x i - centroid K i)) ^ 2) =
      (fun x => ∑ i, ∑ j, (u i * (x i - centroid K i)) *
        (u j * (x j - centroid K j))) by
    funext x
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j)]
  simp only [dotProduct, Matrix.mulVec, covMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show (fun x : EuclideanSpace ℝ (Fin n) =>
      (u i * (x i - centroid K i)) * (u j * (x j - centroid K j))) =
      (fun x => (u i * u j) * ((x i - centroid K i) * (x j - centroid K j))) by
    funext x
    ring, integral_const_mul]
  ring

/-- Covariance matrices of compact sets are positive semidefinite. -/
theorem covMatrix_posSemidef {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) : (covMatrix K).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (covMatrix_isHermitian K)
  intro u
  simp only [star_trivial]
  rw [covMatrix_quadratic hK]
  exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
    (integral_nonneg (fun _ => sq_nonneg _))

/-- The covariance determinant of a compact set is nonnegative. -/
theorem covMatrix_det_nonneg {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) : 0 ≤ (covMatrix K).det :=
  (covMatrix_posSemidef hK).det_nonneg

/-- Nonempty interior makes the covariance quadratic form strictly positive. -/
theorem body_covMatrix_posDef {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsConvexBody K) : (covMatrix K).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (covMatrix_isHermitian K)
  intro u hu
  simp only [star_trivial]
  rw [covMatrix_quadratic hK.isCompact]
  apply mul_pos (inv_pos.mpr (body_vol_pos hK))
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      (∑ i, u i * (x i - centroid K i)) ^ 2) := by fun_prop
  have hi := ContinuousOn.integrableOn_compact (μ := volume) hK.isCompact hc.continuousOn
  by_contra h
  have hzero : (∫ x in K, (∑ i, u i * (x i - centroid K i)) ^ 2) = 0 :=
    le_antisymm (le_of_not_gt h) (integral_nonneg (fun _ => sq_nonneg _))
  have hae := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).mp hzero
  have hpoint := Measure.eqOn_open_of_ae_eq
    (ae_restrict_of_ae_restrict_of_subset interior_subset hae)
    isOpen_interior hc.continuousOn continuousOn_const
  let F : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := ∑ i, u i • EuclideanSpace.proj i
  have hF (x : EuclideanSpace ℝ (Fin n)) : F x = ∑ i, u i * x i := by
    simp [F, EuclideanSpace.proj]
  have hAff : F.toLinearMap.toAffineMap =
      AffineMap.const ℝ (EuclideanSpace ℝ (Fin n)) (F (centroid K)) := by
    apply AffineMap.ext_on (isOpen_interior.affineSpan_eq_top hK.interior_nonempty)
    intro x hx
    change F x = F (centroid K)
    rw [hF, hF, ← sub_eq_zero, ← Finset.sum_sub_distrib]
    simpa only [mul_sub] using (sq_eq_zero_iff.mp (hpoint hx))
  have hlin : F.toLinearMap = 0 := by
    simpa only [LinearMap.toAffineMap_linear, AffineMap.const_linear] using
      congrArg AffineMap.linear hAff
  apply hu
  funext i
  have heval := LinearMap.congr_fun hlin (PiLp.single 2 i (1 : ℝ))
  change F (PiLp.single 2 i (1 : ℝ)) = 0 at heval
  simpa [hF, PiLp.single_apply] using heval

/-- A convex body has strictly positive covariance determinant. -/
theorem body_covMatrix_det_pos {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsConvexBody K) : 0 < (covMatrix K).det :=
  (body_covMatrix_posDef hK).det_pos

end Submission.Lib.ConvexBody
