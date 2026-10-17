import Mathlib
import ChallengeDeps
import Submission.Obl.Entropy__linear_jacobian_normal_form
import Submission.Obl.Entropy__orthogonal_gaussian_exponential_law
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.linear_jacobian_rigidity`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__linear_jacobian_rigidity`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__linear_jacobian_rigidity/`
belong to this obligation.
-/

theorem Submission.Entropy.linear_jacobian_rigidity : ∀ m : ℕ, 1 ≤ m → ∀ F : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), ContDiff ℝ 1 F → MeasureTheory.MemLp F 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) → MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (F) = 0 → ∀ X : Fin m → (Matrix (Fin m) (Fin m) ℝ), (∀ r, (X r).IsHermitian) → Finset.sum Finset.univ (fun r : Fin m => X r * X r) = (1 : (Matrix (Fin m) (Fin m) ℝ)) → (∀ x v i, (fderiv ℝ (F) x v) i = Finset.sum Finset.univ (fun j : Fin m => (cfc (fun t : ℝ => ProbabilityTheory.gaussianPDFReal 0 1 t / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-t)) (Finset.sum Finset.univ (fun r : Fin m => x r • X r))) i j * v j)) → (∃ L : (EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin m)), ∃ a : (EuclideanSpace ℝ (Fin m)), MeasureTheory.Measure.map F (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))).withDensity (fun x => ENNReal.ofReal (|LinearMap.det L.toLinearMap|⁻¹ * (if ∀ i : Fin m, 0 ≤ L.symm (x - a) i then Real.exp (-Finset.sum Finset.univ (fun i : Fin m => L.symm (x - a) i)) else 0)))) ∧ ((fun i j => MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (fun x => F x i * F x j)) = (1 : (Matrix (Fin m) (Fin m) ℝ))) := by
  intro m hm F hF hF2 hcenter X hX hnorm hJac
  obtain ⟨Q, a, hnormal⟩ :=
    Submission.Entropy.linear_jacobian_normal_form m hm F hF X hX hnorm hJac
  obtain ⟨hlaw, hcov⟩ :=
    Submission.Entropy.orthogonal_gaussian_exponential_law m hm F hF2 hcenter Q a hnormal
  exact ⟨⟨Q.toLinearEquiv, a, hlaw⟩, hcov⟩
