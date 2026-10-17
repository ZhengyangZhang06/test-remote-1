import Mathlib
import ChallengeDeps
import Submission.Obl.Entropy__gaussian_covariance_variational.Scalar
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.gaussian_covariance_variational`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__gaussian_covariance_variational`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__gaussian_covariance_variational/`
belong to this obligation.
-/

theorem Submission.Entropy.gaussian_covariance_variational : ∀ m : ℕ, 1 ≤ m → (fun γ => ((fun I => ((fun L2 => ((fun W => (∀ f : (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ x, 0 ≤ f x) → MeasureTheory.Integrable f MeasureTheory.volume → MeasureTheory.integral MeasureTheory.volume f = 1 → MeasureTheory.Integrable (fun x => f x * ‖x‖^2) MeasureTheory.volume → ∀ F : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), ContDiff ℝ 1 F → MeasureTheory.Measure.map F γ = MeasureTheory.Measure.withDensity MeasureTheory.volume (fun x => ENNReal.ofReal (f x)) → ∀ J : (EuclideanSpace ℝ (Fin m)) → (Matrix (Fin m) (Fin m) ℝ), L2 J → (∀ x i j, J x i j = (fderiv ℝ F x (PiLp.single 2 j (1 : ℝ))) i) → ∀ a : (EuclideanSpace ℝ (Fin m)) → (Matrix (Fin m) (Fin m) ℝ), ∀ b : Fin m → (EuclideanSpace ℝ (Fin m)) → (Matrix (Fin m) (Fin m) ℝ), L2 a → (∀ r, L2 (b r)) → (∀ i j, ∀ z : (EuclideanSpace ℝ (Fin m)) → ℝ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z → HasCompactSupport z → I (fun x => (a x i j - J x i j) * z x) = Finset.sum Finset.univ (fun r : Fin m => I (fun x => b r x i j * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ))))) → ∀ P : (Matrix (Fin m) (Fin m) ℝ), P.PosDef → Matrix.trace (P * (Matrix.of (fun i j => MeasureTheory.integral MeasureTheory.volume (fun x => f x * (x i - (MeasureTheory.integral MeasureTheory.volume (fun y => f y • y)) i) * (x j - (MeasureTheory.integral MeasureTheory.volume (fun y => f y • y)) j))))) ≤ W P a + Finset.sum Finset.univ (fun r : Fin m => W P (b r)))) (fun (P : (Matrix (Fin m) (Fin m) ℝ)) (H : (EuclideanSpace ℝ (Fin m)) → (Matrix (Fin m) (Fin m) ℝ)) => I (fun x => Matrix.trace ((H x).transpose * P * H x))))) (fun (H : (EuclideanSpace ℝ (Fin m)) → (Matrix (Fin m) (Fin m) ℝ)) => ∀ i j, MeasureTheory.MemLp (fun x => H x i j) 2 γ))) (MeasureTheory.integral γ))) ((ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))) := by
  intro m hm f hf0 hf hmass hf2 F hF hlaw J hJ hJF a b ha hb hw P hP
  exact Submission.Obl.Entropy__gaussian_covariance_variational.covariance_of_scalar
    (Submission.Obl.Entropy__gaussian_covariance_variational.scalar_covariance_bound m)
    hf0 hf hf2 F hF hlaw J a b hJ hJF ha hb hw P hP
