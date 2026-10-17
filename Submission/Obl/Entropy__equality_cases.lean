import Mathlib
import ChallengeDeps
import Submission.Obl.Entropy__equality_cases.LinearFieldPrimitive
import Submission.Obl.Entropy__equality_cases.EigenvalueLimit
import Submission.Obl.Entropy__equality_cases.GaussianField
import Submission.Obl.Entropy__lower_bound
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.equality_cases`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__equality_cases`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__equality_cases/`
belong to this obligation.
-/

theorem Submission.Entropy.equality_cases : ∀ m : ℕ, 1 ≤ m → ∀ f : (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ x, 0 ≤ f x) → UpperSemicontinuous f → ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) → MeasureTheory.Integrable f MeasureTheory.volume → MeasureTheory.integral MeasureTheory.volume f = 1 → MeasureTheory.Integrable (fun x => f x * ‖x‖ ^ 2) MeasureTheory.volume → MeasureTheory.Integrable (fun x => f x * Real.log (f x)) MeasureTheory.volume → ∀ b : (EuclideanSpace ℝ (Fin m)), b = MeasureTheory.integral MeasureTheory.volume (fun x => f x • x) → ∀ C : Matrix (Fin m) (Fin m) ℝ, C = (fun i j => MeasureTheory.integral MeasureTheory.volume (fun x => f x * (x i - b i) * (x j - b j))) → ∀ H : ℝ, H = -MeasureTheory.integral MeasureTheory.volume (fun x => f x * Real.log (f x)) → (H = (m : ℝ) + Real.log C.det / 2 ↔ ∃ L : (EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin m)), ∃ a : (EuclideanSpace ℝ (Fin m)), ∀ᵐ x ∂MeasureTheory.volume, f x = |LinearMap.det L.toLinearMap|⁻¹ * (if ∀ i : Fin m, 0 ≤ L.symm (x - a) i then Real.exp (-Finset.sum Finset.univ (fun i : Fin m => L.symm (x - a) i)) else 0)) := by
  sorry
