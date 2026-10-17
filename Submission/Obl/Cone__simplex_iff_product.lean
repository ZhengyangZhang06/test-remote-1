import Mathlib
import ChallengeDeps
import Submission.Lib.Cone.Moments
import Submission.Obl.Cone__simplex_iff_product.Simplex
import Submission.Obl.Cone__simplex_iff_product.Normalization
set_option linter.unusedVariables false

/-!
# `Submission.Cone.simplex_iff_product`

An affine product representation identifies the regular closed cone support and
therefore its simplex section. Conversely, lifted simplex vertices give the linear
equivalence; comparison of the cone and product integrals fixes its determinant.

Geometry was developed by session x0006; the normalization helpers and final
assembly were developed by session x0012. The cone mass theorem is imported from
the accepted library contribution of session x0005.
-/

open MeasureTheory
open Submission.Obl.Cone__simplex_iff_product

theorem Submission.Cone.simplex_iff_product : ∀ n : ℕ, 1 ≤ n → ∀ K : Set (EuclideanSpace ℝ (Fin n)), SimplexIsotropic.IsConvexBody K → ∀ f : (EuclideanSpace ℝ (Fin (n + 1))) → ℝ, f = Set.indicator {z | 0 ≤ z 0 ∧ ∃ x ∈ K, ∀ i : Fin n, z i.succ = z 0 * x i} (fun z => Real.exp (-z 0) / ((n.factorial : ℝ) * SimplexIsotropic.vol K)) → ((∃ L : (EuclideanSpace ℝ (Fin (n + 1))) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin (n + 1))), ∃ a : (EuclideanSpace ℝ (Fin (n + 1))), ∀ᵐ x ∂MeasureTheory.volume, f x = |LinearMap.det L.toLinearMap|⁻¹ * (if ∀ i : Fin (n + 1), 0 ≤ L.symm (x - a) i then Real.exp (-Finset.sum Finset.univ (fun i : Fin (n + 1) => L.symm (x - a) i)) else 0)) ↔ SimplexIsotropic.IsSimplex K) := by
  classical
  intro n hn K hK f hf
  constructor
  · rintro ⟨L, a, he⟩
    apply simplex_of_affine_cone hK L a
    apply support_eq hK L a
    simpa only [hf, cone] using he
  · intro hsimplex
    obtain ⟨L, hsupport, hheight⟩ := simplex_linearEquiv hsimplex
    have hmass : ∫ x, f x = 1 := by
      rw [hf]
      exact Submission.Lib.Cone.density_integral hK
    have hpref := cone_prefactor f hf hmass L hsupport hheight
    refine ⟨L, 0, Filter.Eventually.of_forall ?_⟩
    intro z
    simp only [sub_zero, hpref, hheight]
    rw [hf]
    change (cone K).indicator
      (fun w => Real.exp (-w 0) / ((n.factorial : ℝ) * SimplexIsotropic.vol K)) z = _
    by_cases hz : z ∈ cone K
    · have ho := (hsupport z).mp hz
      rw [Set.indicator_of_mem hz, if_pos ho]
      rw [div_eq_mul_inv, mul_comm]
    · have ho : ¬ ∀ i, 0 ≤ L.symm z i := fun h => hz ((hsupport z).mpr h)
      rw [Set.indicator_of_notMem hz, if_neg ho, mul_zero]
