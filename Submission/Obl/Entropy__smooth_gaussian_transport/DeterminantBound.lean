import Submission.Obl.Entropy__smooth_gaussian_transport.DeterminantConcavity

open Set
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem operator_det_smul {m : ℕ} (c : ℝ) (A : E m →L[ℝ] E m) :
    (c • A).det = c ^ m * A.det := by
  rw [← operatorMatrix_det]
  simp only [operatorMatrix, ContinuousLinearMap.toLinearMap_smul, map_smul,
    Matrix.det_smul, Fintype.card_fin, LinearMap.det_toMatrix]

/-- A dimensional determinant bound; no optimal constant is needed in the
contact-measure argument. -/
theorem exists_operator_det_bound {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : E m →L[ℝ] E m, |A.det| ≤ C * ‖A‖ ^ m := by
  obtain ⟨C, hC, hb⟩ := ((isCompact_closedBall (0 : E m →L[ℝ] E m) 1).image
    ContinuousLinearMap.continuous_det).isBounded.exists_pos_norm_le
  refine ⟨C, hC, ?_⟩
  intro A
  by_cases hA : A = 0
  · have hz : (0 : E m →L[ℝ] E m).det = 0 := by
      have he := operator_det_smul (m := m) 0 (ContinuousLinearMap.id ℝ (E m))
      have he0 : (0 : ℝ) • ContinuousLinearMap.id ℝ (E m) = (0 : E m →L[ℝ] E m) := by
        ext v
        simp
      rw [he0, zero_pow (by omega : m ≠ 0), zero_mul] at he
      exact he
    simp only [hA, hz, abs_zero, norm_zero, zero_pow (by omega : m ≠ 0), mul_zero, le_refl]
  have hn : 0 < ‖A‖ := norm_pos_iff.mpr hA
  let B : E m →L[ℝ] E m := ‖A‖⁻¹ • A
  have hBn : ‖B‖ = 1 := by
    simp only [B, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ hn.ne'
  have hdet : |B.det| ≤ C := by
    have hh := hb B.det (mem_image_of_mem _ (by
      simpa only [Metric.mem_closedBall, dist_zero_right, hBn] using (le_refl (1 : ℝ))))
    simpa only [Real.norm_eq_abs] using hh
  have hAB : ‖A‖ • B = A := by
    dsimp [B]
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  calc
    |A.det| = ‖A‖ ^ m * |B.det| := by
      conv_lhs => rw [← hAB, operator_det_smul]
      rw [abs_mul, abs_pow, abs_norm]
    _ ≤ ‖A‖ ^ m * C := mul_le_mul_of_nonneg_left hdet (by positivity)
    _ = C * ‖A‖ ^ m := mul_comm _ _

end Submission.Obl.Entropy__smooth_gaussian_transport
