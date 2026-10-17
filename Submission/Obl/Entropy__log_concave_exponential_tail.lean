import Mathlib
import ChallengeDeps
import Submission.Obl.Entropy__log_concave_exponential_tail.Levels
import Submission.Obl.Entropy__log_concave_exponential_tail.Rays
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.log_concave_exponential_tail`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__log_concave_exponential_tail`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__log_concave_exponential_tail/`
belong to this obligation.
-/

theorem Submission.Entropy.log_concave_exponential_tail : ∀ m : ℕ, 1 ≤ m → ∀ f : (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ x, 0 ≤ f x) → UpperSemicontinuous f → ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) → MeasureTheory.Integrable f MeasureTheory.volume → MeasureTheory.integral MeasureTheory.volume f = 1 → ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧ ∀ x, f x ≤ Real.exp (b - a * ‖x‖) := by
  intro m hm f hf0 hfuc hfconc hfint hfmass
  obtain ⟨t, c, ht, hc, hbound⟩ :=
    Submission.Obl.Entropy__log_concave_exponential_tail.exists_bounded_superlevel
      hf0 hfuc hfconc hfint hfmass
  exact Submission.Obl.Entropy__log_concave_exponential_tail.exponential_bound_of_bounded_superlevel
    hfuc hfconc ht hc hbound
