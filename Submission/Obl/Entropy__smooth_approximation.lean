import Mathlib
import ChallengeDeps
import Submission.Obl.Entropy__smooth_approximation.Construction
import Submission.Obl.Entropy__smooth_approximation.Tails
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.smooth_approximation`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__smooth_approximation`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__smooth_approximation/`
belong to this obligation.
-/

theorem Submission.Entropy.smooth_approximation : ∀ m : ℕ, 1 ≤ m → (fun (density : ((EuclideanSpace ℝ (Fin m)) → ℝ) → (EuclideanSpace ℝ (Fin m)) → ℝ) => (fun (mean : ((EuclideanSpace ℝ (Fin m)) → ℝ) → (EuclideanSpace ℝ (Fin m))) => (fun (covariance : ((EuclideanSpace ℝ (Fin m)) → ℝ) → (Matrix (Fin m) (Fin m) ℝ)) => (fun (entropy : ((EuclideanSpace ℝ (Fin m)) → ℝ) → ℝ) => (fun (regular : ((EuclideanSpace ℝ (Fin m)) → ℝ) → Prop) => ∀ f : (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ x, 0 ≤ f x) → UpperSemicontinuous f → ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) → MeasureTheory.Integrable f MeasureTheory.volume → MeasureTheory.integral MeasureTheory.volume f = 1 → MeasureTheory.Integrable (fun x => f x * ‖x‖ ^ 2) MeasureTheory.volume → MeasureTheory.Integrable (fun x => f x * Real.log (f x)) MeasureTheory.volume → ∃ V : ℕ → (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ n, regular (V n)) ∧ Filter.Tendsto (fun n => entropy (density (V n))) Filter.atTop (nhds (entropy f)) ∧ (∀ i j, Filter.Tendsto (fun n => covariance (density (V n)) i j) Filter.atTop (nhds (covariance f i j))) ∧ Filter.Tendsto (fun n => mean (density (V n))) Filter.atTop (nhds (mean f)) ∧ Filter.Tendsto (fun n => MeasureTheory.integral MeasureTheory.volume (fun x => |density (V n) x - f x|)) Filter.atTop (nhds 0)) (fun V => ContDiff ℝ ((⊤ : ENat) : WithTop ENat) V ∧ (∃ cmin cmax : ℝ, 0 < cmin ∧ cmin ≤ cmax ∧ ∀ x v : (EuclideanSpace ℝ (Fin m)), cmin * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v ∧ (fderiv ℝ (fderiv ℝ V) x v) v ≤ cmax * ‖v‖ ^ 2) ∧ MeasureTheory.Integrable (density V) MeasureTheory.volume ∧ MeasureTheory.integral MeasureTheory.volume (density V) = 1 ∧ MeasureTheory.Integrable (fun x => density V x * ‖x‖ ^ 2) MeasureTheory.volume ∧ MeasureTheory.Integrable (fun x => density V x * Real.log (density V x)) MeasureTheory.volume)) (fun f => -MeasureTheory.integral MeasureTheory.volume (fun x => f x * Real.log (f x)))) (fun f => Matrix.of (fun i j => MeasureTheory.integral MeasureTheory.volume (fun x => f x * (x i - mean f i) * (x j - mean f j))))) (fun f => MeasureTheory.integral MeasureTheory.volume (fun x => f x • x))) (fun V x => Real.exp (-V x)) := by
  intro m hm f hf0 husc hconc hf hmass hf2 hfent
  obtain ⟨a, B, ha, hB, U, hU, htail, hlim⟩ :=
    Submission.Obl.Entropy__smooth_approximation.smooth_sequence_of_log_concave
      hm hf0 husc hconc hf hmass
  obtain ⟨V, hV, hentropy, hcov, hmean, hL1⟩ :=
    Submission.Obl.Entropy__smooth_approximation.approximation_of_linear_tail
      hf0 hf hmass hf2 hU ha htail (Filter.Eventually.of_forall hlim)
  refine ⟨V, ?_, hentropy, hcov, hmean, hL1⟩
  intro n
  rcases hV n with ⟨⟨hsmooth, hhessian⟩, hint, hnorm, hmoment, hent⟩
  exact ⟨hsmooth, hhessian, hint, hnorm, hmoment, hent⟩
