import Submission.Obl.Entropy__linear_jacobian_normal_form.GaussianCompatibility
import Submission.Obl.Entropy__linear_jacobian_normal_form.SignedEigenbasis
import Submission.Obl.Entropy__linear_jacobian_normal_form.EigenbasisPrimitive

open scoped BigOperators

open Submission.Obl.Entropy__linear_jacobian_normal_form
open Submission.Lib.JacobianCompatibility

/-- The orthogonal coordinate normal form of a normalized Gaussian-hazard Jacobian. -/
theorem Submission.Entropy.linear_jacobian_normal_form :
    ∀ m : ℕ, 1 ≤ m →
    ∀ F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m),
    ContDiff ℝ 1 F →
    ∀ X : Fin m → Matrix (Fin m) (Fin m) ℝ,
    (∀ r, (X r).IsHermitian) →
    (∑ r, X r * X r) = 1 →
    (∀ x v i, fderiv ℝ F x v i =
      ∑ j, cfc (fun t : ℝ ↦ ProbabilityTheory.gaussianPDFReal 0 1 t /
        ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-t))
        (∑ r, x r • X r) i j * v j) →
    ∃ Q : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m),
    ∃ a : EuclideanSpace ℝ (Fin m), ∀ x i,
      Q.symm (F (Q x) - a) i =
        -Real.log (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-x i)) := by
  intro m hm F hF X hX hnorm hJ
  obtain ⟨hlin, hquad⟩ := gaussian_jacobian_coefficient_identities F hF X hX hJ
  obtain ⟨b, hb⟩ := unsigned_eigenbasis X hX hlin hquad hnorm
  have hA (x : EuclideanSpace ℝ (Fin m)) : (∑ r, x r • X r).IsHermitian := by
    simpa only [coefficientField_apply] using coefficientField_isHermitian X hX x
  obtain ⟨a, ha⟩ := gaussian_primitive_of_eigenbasis F hF
    (fun x ↦ ∑ r, x r • X r) hA hJ b hb
  exact ⟨b.repr.symm, a, ha⟩
