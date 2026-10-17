import Mathlib
import ChallengeDeps
import Submission.Obl.Cone__moments
import Submission.Obl.Cone__simplex_iff_product.Simplex
import Submission.Obl.Cone__simplex_iff_product.Normalization
set_option linter.unusedVariables false

/-!
# `Submission.Cone.simplex_iff_product`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Cone__simplex_iff_product`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Cone__simplex_iff_product/`
belong to this obligation.
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
    let b := ∫ x, f x • x
    let C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      fun i j => ∫ x, f x * (x i - b i) * (x j - b j)
    let H := -(∫ x, f x * Real.log (f x))
    have hmom := Submission.Cone.moments n hn K hK f hf b rfl C rfl H rfl
    obtain ⟨_, _, _, _, _, _, hmass, _⟩ := hmom
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
