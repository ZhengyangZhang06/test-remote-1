import Mathlib
import ChallengeDeps
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.mollified_convex_sequence`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__mollified_convex_sequence`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__mollified_convex_sequence/`
belong to this obligation.
-/

theorem Submission.Entropy.mollified_convex_sequence : ∀ m : ℕ, 1 ≤ m → ∀ Q : ℕ → (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ n, ContDiff ℝ 1 (Q n) ∧ ConvexOn ℝ Set.univ (Q n) ∧ ∀ x y : (EuclideanSpace ℝ (Fin m)), ‖fderiv ℝ (Q n) x - fderiv ℝ (Q n) y‖ ≤ ((n : ℝ) + 1) * ‖x - y‖) → ∃ U : ℕ → (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ n, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (U n) ∧ ∀ x v : (EuclideanSpace ℝ (Fin m)), (2 / ((n : ℝ) + 1)) * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ (U n)) x v) v ∧ (fderiv ℝ (fderiv ℝ (U n)) x v) v ≤ ((n : ℝ) + 1 + 2 / ((n : ℝ) + 1)) * ‖v‖ ^ 2) ∧ (∀ n x, Q n x ≤ U n x) ∧ ∀ x, Filter.Tendsto (fun n => U n x - Q n x) Filter.atTop (nhds 0) := by
  sorry
