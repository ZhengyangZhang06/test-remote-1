import Mathlib
import ChallengeDeps
import Submission.Obl.Entropy__moreau_envelope_sequence.Minimizer
import Submission.Obl.Entropy__moreau_envelope_sequence.Regularity
import Submission.Obl.Entropy__moreau_envelope_sequence.Limit
set_option linter.unusedVariables false

open Submission.Obl.Entropy__moreau_envelope_sequence

/-!
# `Submission.Entropy.moreau_envelope_sequence`

Maximize the Gaussian-weighted density to construct each proximal point.
Its variational inequality gives a convex C¹ envelope with the sharp
derivative Lipschitz bound. The tail controls the common lower bound;
upper semicontinuity and Gaussian decay give the pointwise density limit.
-/

theorem Submission.Entropy.moreau_envelope_sequence : ∀ m : ℕ, 1 ≤ m → ∀ f : (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ x, 0 ≤ f x) → UpperSemicontinuous f → ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) → (∃ x, 0 < f x) → ∀ a b : ℝ, 0 < a → 0 ≤ b → (∀ x, f x ≤ Real.exp (b - a * ‖x‖)) → ∃ Q : ℕ → (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ n, ContDiff ℝ 1 (Q n) ∧ ConvexOn ℝ Set.univ (Q n) ∧ ∀ x y : (EuclideanSpace ℝ (Fin m)), ‖fderiv ℝ (Q n) x - fderiv ℝ (Q n) y‖ ≤ ((n : ℝ) + 1) * ‖x - y‖) ∧ (∀ n x, a * ‖x‖ - (b + a ^ 2 / 2) ≤ Q n x) ∧ ∀ x, Filter.Tendsto (fun n => Real.exp (-Q n x)) Filter.atTop (nhds (f x)) := by
  classical
  intro m hm f hf hu hc hne a b ha hb htail
  have hex : ∀ (n : ℕ) (x : EuclideanSpace ℝ (Fin m)), ∃ p,
      0 < f p ∧ ∀ y, weight f ((n : ℝ) + 1) x y ≤ weight f ((n : ℝ) + 1) x p := by
    intro n x
    exact exists_weight_max hf hu hne ha (by positivity) htail x
  choose p hp hmax using hex
  have hmin : ∀ (n : ℕ) x y, 0 < f y →
      envelope (fun z => -Real.log (f z)) ((n : ℝ) + 1) (p n) x ≤
        -Real.log (f y) + ((n : ℝ) + 1) / 2 * ‖x - y‖ ^ 2 := by
    intro n x y hy
    exact objective_le_of_weight_le (hp n x) hy (hmax n x y)
  refine ⟨fun n => envelope (fun z => -Real.log (f z)) ((n : ℝ) + 1) (p n), ?_, ?_, ?_⟩
  · intro n
    exact envelope_regular hc.neg (by positivity) (hp n) (hmin n)
  · intro n x
    exact objective_lower_bound ha (le_add_of_nonneg_left (Nat.cast_nonneg n))
      htail x (p n x) (hp n x)
  · intro x
    have hbound : ∀ y, f y ≤ Real.exp b := by
      intro y
      apply (htail y).trans
      exact Real.exp_le_exp.mpr (sub_le_self b (by positivity))
    exact (weight_max_tendsto hf hu hbound x (fun n => p n x) (fun n y => hmax n x y)).congr
      (fun n => weight_eq_exp_objective (hp n x))
