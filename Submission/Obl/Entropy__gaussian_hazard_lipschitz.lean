import Submission.Obl.Entropy__gaussian_hazard_lipschitz.Hazard

/-!
# The standard Gaussian hazard is 1-Lipschitz

The first two moments of a Gaussian truncated to a half-line give
`0 ≤ q' ≤ 1`. The conclusion follows from the mean value inequality.
-/

open Submission.Obl.Entropy__gaussian_hazard_lipschitz

theorem Submission.Entropy.gaussian_hazard_lipschitz : ∀ x y : ℝ, |ProbabilityTheory.gaussianPDFReal 0 1 x / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-x) - ProbabilityTheory.gaussianPDFReal 0 1 y / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-y)| ≤ |x - y| := by
  intro x y
  simpa only [hazard, pdf, ← cdf_eq_mass] using hazard_lipschitz x y
