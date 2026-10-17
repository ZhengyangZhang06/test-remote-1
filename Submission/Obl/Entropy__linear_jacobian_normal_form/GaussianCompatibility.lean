/-
Adapted from: here:o011

Original tree proofs by sessions x0028, x0067, and x0068.
-/

import Submission.Lib.JacobianCompatibility
import Submission.Obl.Entropy__linear_jacobian_normal_form.HazardCoefficients

namespace Submission.Obl.Entropy__linear_jacobian_normal_form

open scoped BigOperators
open Submission.Lib.JacobianCompatibility

/-- The two compatibility identities for the exact Gaussian-hazard Jacobian. -/
theorem gaussian_jacobian_coefficient_identities
    {n : Type*} [Fintype n] [DecidableEq n]
    (F : EuclideanSpace ℝ n → EuclideanSpace ℝ n) (hF : ContDiff ℝ 1 F)
    (X : n → Matrix n n ℝ) (hX : ∀ r, (X r).IsHermitian)
    (hJ : ∀ x v i, fderiv ℝ F x v i =
      ∑ j, cfc (fun t : ℝ ↦ ProbabilityTheory.gaussianPDFReal 0 1 t /
        ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-t))
        (∑ r, x r • X r) i j * v j) :
    (∀ r s i, X r i s = X s i r) ∧
    (∀ r s t i, (X r * X t + X t * X r) i s = (X s * X t + X t * X s) i r) := by
  obtain ⟨hqc, hq1, hq2⟩ := gaussian_hazard_coefficients
  exact jacobian_coefficient_identities X hX hqc hq1 hq2
    (hF.differentiable (by norm_num)) hJ

end Submission.Obl.Entropy__linear_jacobian_normal_form
