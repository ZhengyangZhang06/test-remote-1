import Mathlib
import ChallengeDeps
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.smooth_gaussian_transport`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__smooth_gaussian_transport`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__smooth_gaussian_transport/`
belong to this obligation.
-/

theorem Submission.Entropy.smooth_gaussian_transport : ∀ m : ℕ, 1 ≤ m → (fun (H : ((EuclideanSpace ℝ (Fin m)) → ℝ) → ℝ → ℝ → Prop) => (fun (regular : ((EuclideanSpace ℝ (Fin m)) → ℝ) → Prop) => (fun (T : ((EuclideanSpace ℝ (Fin m)) → ℝ) → ((EuclideanSpace ℝ (Fin m)) → ℝ) → Prop) => ∀ V : ((EuclideanSpace ℝ (Fin m)) → ℝ), regular V → ∃ φ : ((EuclideanSpace ℝ (Fin m)) → ℝ), T V φ) (fun U φ : ((EuclideanSpace ℝ (Fin m)) → ℝ) => ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ ∧ ConvexOn ℝ Set.univ φ ∧ MeasureTheory.Measure.map (gradient φ) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) = MeasureTheory.Measure.withDensity MeasureTheory.volume (fun x => ENNReal.ofReal (Real.exp (-U x))))) (fun V : ((EuclideanSpace ℝ (Fin m)) → ℝ) => ContDiff ℝ ((⊤ : ENat) : WithTop ENat) V ∧ (∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ H V a b) ∧ MeasureTheory.Integrable (fun x => Real.exp (-V x)) MeasureTheory.volume ∧ MeasureTheory.integral MeasureTheory.volume (fun x => Real.exp (-V x)) = 1 ∧ MeasureTheory.Integrable (fun x => Real.exp (-V x) * ‖x‖ ^ 2) MeasureTheory.volume ∧ MeasureTheory.Integrable (fun x => Real.exp (-V x) * Real.log (Real.exp (-V x))) MeasureTheory.volume)) (fun (F : ((EuclideanSpace ℝ (Fin m)) → ℝ)) (a b : ℝ) => ∀ x v : (EuclideanSpace ℝ (Fin m)), a * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v ∧ (fderiv ℝ (fderiv ℝ F) x v) v ≤ b * ‖v‖ ^ 2) := by
  sorry
