import Mathlib
import ChallengeDeps
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.lower_bound`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__lower_bound`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__lower_bound/`
belong to this obligation.
-/

theorem Submission.Entropy.lower_bound : ∀ m : ℕ, 1 ≤ m → ∀ f : (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ x, 0 ≤ f x) → UpperSemicontinuous f → ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) → MeasureTheory.Integrable f MeasureTheory.volume → MeasureTheory.integral MeasureTheory.volume f = 1 → MeasureTheory.Integrable (fun x => f x * ‖x‖ ^ 2) MeasureTheory.volume → MeasureTheory.Integrable (fun x => f x * Real.log (f x)) MeasureTheory.volume → ∀ b : (EuclideanSpace ℝ (Fin m)), b = MeasureTheory.integral MeasureTheory.volume (fun x => f x • x) → ∀ C : Matrix (Fin m) (Fin m) ℝ, C = (fun i j => MeasureTheory.integral MeasureTheory.volume (fun x => f x * (x i - b i) * (x j - b j))) → ∀ H : ℝ, H = -MeasureTheory.integral MeasureTheory.volume (fun x => f x * Real.log (f x)) → (m : ℝ) + Real.log C.det / 2 ≤ H := by
  sorry
