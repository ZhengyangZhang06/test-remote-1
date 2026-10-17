import Mathlib
import ChallengeDeps
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.log_concave_exponential_tail`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__log_concave_exponential_tail`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__log_concave_exponential_tail/`
belong to this obligation.
-/

theorem Submission.Entropy.log_concave_exponential_tail : ∀ m : ℕ, 1 ≤ m → ∀ f : (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ x, 0 ≤ f x) → UpperSemicontinuous f → ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) → MeasureTheory.Integrable f MeasureTheory.volume → MeasureTheory.integral MeasureTheory.volume f = 1 → ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧ ∀ x, f x ≤ Real.exp (b - a * ‖x‖) := by
  sorry
