import Mathlib
import ChallengeDeps
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.moreau_envelope_sequence`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__moreau_envelope_sequence`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__moreau_envelope_sequence/`
belong to this obligation.
-/

theorem Submission.Entropy.moreau_envelope_sequence : ∀ m : ℕ, 1 ≤ m → ∀ f : (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ x, 0 ≤ f x) → UpperSemicontinuous f → ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) → (∃ x, 0 < f x) → ∀ a b : ℝ, 0 < a → 0 ≤ b → (∀ x, f x ≤ Real.exp (b - a * ‖x‖)) → ∃ Q : ℕ → (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ n, ContDiff ℝ 1 (Q n) ∧ ConvexOn ℝ Set.univ (Q n) ∧ ∀ x y : (EuclideanSpace ℝ (Fin m)), ‖fderiv ℝ (Q n) x - fderiv ℝ (Q n) y‖ ≤ ((n : ℝ) + 1) * ‖x - y‖) ∧ (∀ n x, a * ‖x‖ - (b + a ^ 2 / 2) ≤ Q n x) ∧ ∀ x, Filter.Tendsto (fun n => Real.exp (-Q n x)) Filter.atTop (nhds (f x)) := by
  sorry
