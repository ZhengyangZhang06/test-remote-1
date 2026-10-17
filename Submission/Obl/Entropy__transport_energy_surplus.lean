import Mathlib
import ChallengeDeps
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.transport_energy_surplus`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__transport_energy_surplus`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__transport_energy_surplus/`
belong to this obligation.
-/

theorem Submission.Entropy.transport_energy_surplus : ∀ m : ℕ, 1 ≤ m → ∀ A : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ, ∀ hA : ∀ x, (A x).IsHermitian, (fun q => (fun J => (fun γ => (fun L2 => (fun d => (fun Z => (fun t => (fun k => (fun K => (fun I => (fun N => (fun δ => (fun σ => (fun U => (fun sep => (fun ka => (∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => A x i j)) → (∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) → ∀ V φ : (EuclideanSpace ℝ (Fin m)) → ℝ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) V → (∃ cmin cmax : ℝ, 0 < cmin ∧ cmin ≤ cmax ∧ ∀ x v : (EuclideanSpace ℝ (Fin m)), cmin * ‖v‖^2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v ∧ (fderiv ℝ (fderiv ℝ V) x v) v ≤ cmax * ‖v‖^2) → ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ → ConvexOn ℝ Set.univ φ → (∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (PiLp.single 2 j (1 : ℝ))) i) → MeasureTheory.Measure.map (gradient φ) γ = MeasureTheory.Measure.withDensity MeasureTheory.volume (fun x => ENNReal.ofReal (Real.exp (-V x))) → (∀ r, L2 (Z r)) ∧ (∀ r, L2 (K r)) ∧ Finset.sum Finset.univ (fun r : Fin m => N (Z r)) - Finset.sum Finset.univ (fun r : Fin m => N (K r)) + sep ≤ N ka) (fun x => cfc k (A x))) (I (fun x => Finset.sum Finset.univ (fun r : Fin m => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => σ ((hA x).eigenvalues i) ((hA x).eigenvalues j) * ((U x).transpose * Z r x * U x) i j ^ 2)))))) (fun x => ((hA x).eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ))) (fun a b => (1 + (if min a b < -3 then 0 else if min a b < -2 then 19/100 else if min a b < -1 then 38/100 else 68/100)) / 16 * (1 + (δ a b)^2/30 + (δ a b)^4/1680) * (δ a b)^2)) (fun a b => Real.log (q a) - Real.log (q b))) (fun F => I (fun x => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (F x i j)^2))))) (MeasureTheory.integral γ)) (d (fun x => cfc k (A x)))) (fun a => t a / q a)) (fun a => -Real.log (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a)))) (d A)) (fun F r x => Matrix.of (fun i j => fderiv ℝ (fun y => F y i j) x (PiLp.single 2 r (1 : ℝ))))) (fun F => ∀ i j, MeasureTheory.MemLp (fun x => F x i j) 2 γ)) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))) (fun x => cfc q (A x))) (fun a => ProbabilityTheory.gaussianPDFReal 0 1 a / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a)) := by
  sorry
