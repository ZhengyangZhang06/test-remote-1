import Mathlib
import ChallengeDeps
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.first_chaos_absorption`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__first_chaos_absorption`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__first_chaos_absorption/`
belong to this obligation.
-/

theorem Submission.Entropy.first_chaos_absorption : ∀ m : ℕ, 1 ≤ m → ∀ A : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ, ∀ hA : ∀ x, (A x).IsHermitian, (fun γ => (fun I => (fun X => (fun B => (fun Y => (fun S => (fun t => (fun q => (fun k => (fun b => (fun l => (fun p => (fun h => (fun cost => (fun R => (fun N => (fun ω => (∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => A x i j)) → (∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) → (∀ i j, I (fun x => A x i j) = 0) → ∀ hB : B.PosSemidef, R ≤ (69/500)*N Y - Finset.sum Finset.univ (fun i : Fin m => ω (hB.isHermitian.eigenvalues i))/1000) (fun z => (3 * (z - 1)^2 / (37 + 3*z)) * ((3 : ℝ)/20 + ((49 : ℝ)/100)*(37/(37+3*z))) * (if z = 0 then (13 : ℝ)/100 else min ((13 : ℝ)/100) (32/(25*Real.sqrt z))))) (fun F => I (fun x => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (F x i j)^2))))) (Matrix.trace (S - 1) - Real.log S.det - I (fun x => Matrix.trace ((-(S - 1) * (B - 1)) * ((3/20 : ℝ) • 1 + (1813/4000 : ℝ) • S) * cfc p (A x))) + I (fun x => Matrix.trace (Y x * Y x * cfc cost (A x))))) (fun a => (40/37) * ((b a - 7/25)^2 + (5/96) * (h a)^2 / p a))) (fun a => k a * (1 + b a) - (3/2) * k a - (80/3) * (b a - 7/25) * l a)) (fun a => deriv (fun z => k z * (1 + b z)) a - (b a)^2 - (40/3) * (l a)^2)) (deriv b)) (deriv k)) (fun a => t a / q a)) (fun a => ProbabilityTheory.gaussianPDFReal 0 1 a / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a))) (fun a => -Real.log (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a)))) (((37/40 : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ) + (3/40 : ℝ) • B)⁻¹)) (fun x => A x - Finset.sum Finset.univ (fun r : Fin m => x r • X r))) (Finset.sum Finset.univ (fun r : Fin m => X r * X r))) (fun r => Matrix.of (fun i j => I (fun x => x r * A x i j)))) (MeasureTheory.integral γ)) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  sorry
