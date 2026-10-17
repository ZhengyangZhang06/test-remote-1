import Mathlib
import ChallengeDeps
import Submission.Obl.Entropy__absorption_h_square_bound.Covered
set_option linter.unusedVariables false

/-!
# Gaussian absorption square bound on the compact interval

The accepted compact Gaussian approximations reduce the bound to eleven exact
rational polynomial certificates, checked by the kernel in `Checks.lean`.
-/

open Submission.Obl.Entropy__two_eigenvalue_compact_certificate in
theorem Submission.Entropy.absorption_h_square_bound : ∀ a : ℝ, -6 ≤ a → a ≤ 10 → (fun t : ℝ → ℝ => (fun q : ℝ → ℝ => (fun k : ℝ → ℝ => (fun b : ℝ → ℝ => (fun l : ℝ → ℝ => (fun p : ℝ → ℝ => (fun h : ℝ → ℝ => (h a)^2 ≤ ((67/100 : ℝ)^2) * p a) (fun a => k a * (1 + b a) - (3/2) * k a - (80/3) * (b a - 7/25) * l a)) (fun a => deriv (fun z => k z * (1 + b z)) a - (b a)^2 - (40/3) * (l a)^2)) (deriv b)) (deriv k)) (fun a => t a / q a)) (fun a => ProbabilityTheory.gaussianPDFReal 0 1 a / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a))) (fun a => -Real.log (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a))) := by
  intro a ha hb
  change (k a*(1+b a)-(3/2)*k a-(80/3)*(b a-7/25)*l a)^2 ≤
    (67/100 : ℝ)^2 * p a
  exact Submission.Obl.Entropy__absorption_h_square_bound.compact_square_bound a ha hb
