import Mathlib
import ChallengeDeps
import Submission.Obl.Entropy__absorption_p_lower_bounds.Intervals
set_option linter.unusedVariables false

/-!
# Compact Gaussian reserve bounds

The accepted compact Gaussian polynomial enclosures give the three reserve
lower bounds after exact rational Bernstein checks on eleven covering intervals.
-/

theorem Submission.Entropy.absorption_p_lower_bounds : ∀ a : ℝ, -6 ≤ a → a ≤ 10 → (fun t : ℝ → ℝ => (fun q : ℝ → ℝ => (fun k : ℝ → ℝ => (fun b : ℝ → ℝ => (fun l : ℝ → ℝ => (fun p : ℝ → ℝ => (a ≤ 0 → 1 / (7 + a^2) ≤ p a) ∧ (0 ≤ a → (1/4 : ℝ) ≤ p a) ∧ (4 ≤ a → (23/50 : ℝ) ≤ p a)) (fun a => deriv (fun z => k z * (1 + b z)) a - (b a)^2 - (40/3) * (l a)^2)) (deriv b)) (deriv k)) (fun a => t a / q a)) (fun a => ProbabilityTheory.gaussianPDFReal 0 1 a / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a))) (fun a => -Real.log (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a))) := by
  intro a ha hb
  change (a ≤ 0 → 1/(7+a^2) ≤ Submission.Obl.Entropy__two_eigenvalue_compact_certificate.p a) ∧
    (0 ≤ a → (1/4 : ℝ) ≤ Submission.Obl.Entropy__two_eigenvalue_compact_certificate.p a) ∧
    (4 ≤ a → (23/50 : ℝ) ≤ Submission.Obl.Entropy__two_eigenvalue_compact_certificate.p a)
  exact ⟨fun h => Submission.Obl.Entropy__absorption_p_lower_bounds.negative_bound ha h,
    fun h => Submission.Obl.Entropy__absorption_p_lower_bounds.positive_bound h hb,
    fun h => Submission.Obl.Entropy__absorption_p_lower_bounds.large_positive_bound h hb⟩
