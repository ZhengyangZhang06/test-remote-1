import Mathlib
import ChallengeDeps

open MeasureTheory

namespace Submission.Obl.Cone__simplex_iff_product

theorem orthant_exp_integral (m : ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin m),
      if ∀ i, 0 ≤ x i then Real.exp (-∑ i, x i) else 0) = 1 := by
  classical
  have hprod (x : Fin m → ℝ) :
      (if ∀ i, 0 ≤ x i then Real.exp (-∑ i, x i) else 0) =
        ∏ i, (Set.Ici (0 : ℝ)).indicator (fun t => Real.exp (-t)) (x i) := by
    by_cases hx : ∀ i, 0 ≤ x i
    · rw [if_pos hx, ← Finset.sum_neg_distrib, Real.exp_sum]
      apply Finset.prod_congr rfl
      intro i hi
      simp [Set.indicator_of_mem, hx i]
    · rw [if_neg hx]
      obtain ⟨i, hi⟩ := not_forall.mp hx
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
  rw [← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)).symm.integral_comp']
  change (∫ x : Fin m → ℝ,
    if ∀ i, 0 ≤ x i then Real.exp (-∑ i, x i) else 0) = 1
  simp_rw [hprod]
  rw [integral_fintype_prod_volume_eq_prod]
  simp_rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_exp_neg_Ioi_zero]
  simp

theorem integral_comp_linearEquiv {m : ℕ}
    (L : EuclideanSpace ℝ (Fin m) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (g : EuclideanSpace ℝ (Fin m) → ℝ) :
    (∫ x, g (L x)) = |LinearMap.det L.toLinearMap|⁻¹ * ∫ x, g x := by
  have hm : (∫ y, g y ∂Measure.map L.toLinearMap volume) = ∫ x, g (L x) :=
    integral_map_equiv (μ := volume)
      L.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv g
  rw [← hm]
  change (∫ y, g y ∂Measure.map L.toLinearMap volume) = _
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume L.isUnit_det'.ne_zero,
    integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul, abs_inv]

theorem cone_prefactor {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hf : f = Set.indicator
      {z | 0 ≤ z 0 ∧ ∃ x ∈ K, ∀ i : Fin n, z i.succ = z 0 * x i}
      (fun z => Real.exp (-z 0) / ((n.factorial : ℝ) * SimplexIsotropic.vol K)))
    (hmass : ∫ x, f x = 1)
    (L : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (hsupport : ∀ z : EuclideanSpace ℝ (Fin (n + 1)),
      (0 ≤ z 0 ∧ ∃ x ∈ K, ∀ i : Fin n, z i.succ = z 0 * x i) ↔
        ∀ i, 0 ≤ L.symm z i)
    (hheight : ∀ z : EuclideanSpace ℝ (Fin (n + 1)), ∑ i, L.symm z i = z 0) :
    |LinearMap.det L.toLinearMap|⁻¹ =
      ((n.factorial : ℝ) * SimplexIsotropic.vol K)⁻¹ := by
  classical
  have hpull (x : EuclideanSpace ℝ (Fin (n + 1))) :
      f (L x) = (if ∀ i, 0 ≤ x i then Real.exp (-∑ i, x i) else 0) /
        ((n.factorial : ℝ) * SimplexIsotropic.vol K) := by
    rw [hf]
    by_cases hx : ∀ i, 0 ≤ x i
    · have hc := (hsupport (L x)).mpr (by simpa only [L.symm_apply_apply] using hx)
      simp only [Set.indicator, Set.mem_ofPred_eq, if_pos hc, if_pos hx]
      rw [← hheight (L x), L.symm_apply_apply]
    · have hc : ¬ (0 ≤ (L x) 0 ∧ ∃ y ∈ K,
          ∀ i : Fin n, (L x) i.succ = (L x) 0 * y i) := by
        intro hc
        apply hx
        simpa only [L.symm_apply_apply] using (hsupport (L x)).mp hc
      simp only [Set.indicator, Set.mem_ofPred_eq, if_neg hc, if_neg hx, zero_div]
  have hscale := integral_comp_linearEquiv L f
  rw [hmass, mul_one] at hscale
  rw [← hscale]
  simp_rw [hpull]
  rw [integral_div, orthant_exp_integral, one_div]

end Submission.Obl.Cone__simplex_iff_product
