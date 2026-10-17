import Mathlib
import ChallengeDeps
set_option linter.unusedVariables false

/-!
# `Submission.Cone.simplex_iff_product`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Cone__simplex_iff_product`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Cone__simplex_iff_product/`
belong to this obligation.
-/

theorem Submission.Cone.simplex_iff_product : ∀ n : ℕ, 1 ≤ n → ∀ K : Set (EuclideanSpace ℝ (Fin n)), SimplexIsotropic.IsConvexBody K → ∀ f : (EuclideanSpace ℝ (Fin (n + 1))) → ℝ, f = Set.indicator {z | 0 ≤ z 0 ∧ ∃ x ∈ K, ∀ i : Fin n, z i.succ = z 0 * x i} (fun z => Real.exp (-z 0) / ((n.factorial : ℝ) * SimplexIsotropic.vol K)) → ((∃ L : (EuclideanSpace ℝ (Fin (n + 1))) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin (n + 1))), ∃ a : (EuclideanSpace ℝ (Fin (n + 1))), ∀ᵐ x ∂MeasureTheory.volume, f x = |LinearMap.det L.toLinearMap|⁻¹ * (if ∀ i : Fin (n + 1), 0 ≤ L.symm (x - a) i then Real.exp (-Finset.sum Finset.univ (fun i : Fin (n + 1) => L.symm (x - a) i)) else 0)) ↔ SimplexIsotropic.IsSimplex K) := by
  sorry
