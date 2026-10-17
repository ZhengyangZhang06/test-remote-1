import Mathlib
import ChallengeDeps
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.gaussian_chaos_resolvent`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__gaussian_chaos_resolvent`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__gaussian_chaos_resolvent/`
belong to this obligation.
-/

theorem Submission.Entropy.gaussian_chaos_resolvent : ∀ m : ℕ, 1 ≤ m → ∀ A : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ, ∀ hA : ∀ x, (A x).IsHermitian, (fun γ => (fun I => (fun L2 => (fun d => (fun Z => (fun Div => (fun X => (fun Y => (fun N => (∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => A x i j)) → (∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) → (∀ i j, I (fun x => A x i j) = 0) → (∀ r, L2 (Z r)) → ∃ g : Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ), (fun G => (fun Q => (fun QE => (∀ r x, (g r x).IsHermitian) ∧ (∀ r, L2 (g r)) ∧ Div Y g ∧ N A - Finset.sum Finset.univ (fun r : Fin m => N (Z r)) + QE ≤ -(7/50)*N Y) (I (fun x => Finset.sum Finset.univ (fun r : Fin m => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => Q (G r x i j) (g r x i j - G r x i j / 2))))))) (fun a b => (43/100)*a^2 + (26/100)*a*b + (68/25)*b^2)) (d Y)) (fun F => I (fun x => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (F x i j)^2))))) (fun x => A x - Finset.sum Finset.univ (fun r : Fin m => x r • X r))) (fun r => Matrix.of (fun i j => I (fun x => x r * A x i j)))) (fun F v => ∀ i j, ∀ z : (EuclideanSpace ℝ (Fin m)) → ℝ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z → HasCompactSupport z → I (fun x => F x i j * z x) = Finset.sum Finset.univ (fun r : Fin m => I (fun x => v r x i j * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)))))) (d A)) (fun F r x => Matrix.of (fun i j => fderiv ℝ (fun y => F y i j) x (PiLp.single 2 r (1 : ℝ))))) (fun F => ∀ i j, MeasureTheory.MemLp (fun x => F x i j) 2 γ)) (MeasureTheory.integral γ)) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  sorry
