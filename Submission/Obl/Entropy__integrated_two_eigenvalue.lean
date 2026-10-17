import Mathlib
import ChallengeDeps
import Submission.Obl.Entropy__integrated_two_eigenvalue.Interfaces
import Submission.Obl.Entropy__two_eigenvalue_compact_certificate
import Submission.Obl.Entropy__two_eigenvalue_negative_certificate
import Submission.Obl.Entropy__two_eigenvalue_positive_certificate
import Submission.Obl.Entropy__two_eigenvalue_secant_deduction
import Submission.Obl.Entropy__two_eigenvalue_matrix_bridge
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.integrated_two_eigenvalue`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__integrated_two_eigenvalue`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__integrated_two_eigenvalue/`
belong to this obligation.
-/

open Submission.Obl.Entropy__integrated_two_eigenvalue in
theorem Submission.Entropy.integrated_two_eigenvalue : ∀ m : ℕ, 1 ≤ m → ∀ A : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ, ∀ hA : ∀ x, (A x).IsHermitian, (fun γ => (fun I => (fun L2 => (fun d => (fun Z => (fun t => (fun q => (fun k => (fun K => (fun X => (fun Y => (fun b => (fun l => (fun p => (fun δ => (fun σ => (fun U => (fun sep => (∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => A x i j)) → (∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) → (∀ i j, I (fun x => A x i j) = 0) → (∀ r, L2 (Z r)) → (∀ r, L2 (K r)) → ∀ g : Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ), (∀ r x, (g r x).IsHermitian) → (∀ r, L2 (g r)) → (fun N => (fun Dr => (fun Lr => (fun f0 => (fun Mr => (fun PB => (fun G => (fun Q => (fun QE => (∀ a, 0 < p a) ∧ PB ≤ QE + sep) (I (fun x => Finset.sum Finset.univ (fun r : Fin m => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => Q (G r x i j) (g r x i j - G r x i j / 2))))))) (fun a b => (43/100)*a^2 + (26/100)*a*b + (68/25)*b^2)) (d Y)) (Finset.sum Finset.univ (fun r : Fin m => (40/37)*N (fun x => Dr r x - (7/25 : ℝ) • g r x) + (42/37)*N (fun x => Dr r x - (3/4 : ℝ) • g r x) + (27/592)*N (g r) + (40/3)*N (Lr r) + (5/17)*N (fun x => Mr r x * cfc (fun a => (Real.sqrt (p a))⁻¹) (A x))))) (fun r x => d (fun y => cfc f0 (A y)) r x - X r * cfc (deriv f0) (A x) - 2 • (Dr r x * cfc b (A x)) - (80/3 : ℝ) • (Lr r x * cfc l (A x)) + (3/2 : ℝ) • (g r x * cfc b (A x)))) (fun a => k a * (1 + b a))) (fun r x => d (fun y => cfc b (A y)) r x - X r * cfc l (A x))) (fun r x => K r x - X r * cfc b (A x))) (fun F => I (fun x => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (F x i j)^2))))) (I (fun x => Finset.sum Finset.univ (fun r : Fin m => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => σ ((hA x).eigenvalues i) ((hA x).eigenvalues j) * ((U x).transpose * Z r x * U x) i j ^ 2)))))) (fun x => ((hA x).eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ))) (fun a b => (1 + (if min a b < -3 then 0 else if min a b < -2 then 19/100 else if min a b < -1 then 38/100 else 68/100)) / 16 * (1 + (δ a b)^2/30 + (δ a b)^4/1680) * (δ a b)^2)) (fun a b => Real.log (q a) - Real.log (q b))) (fun a => deriv (fun z => k z * (1 + b z)) a - (b a)^2 - (40/3) * (l a)^2)) (deriv b)) (deriv k)) (fun x => A x - Finset.sum Finset.univ (fun r : Fin m => x r • X r))) (fun r => Matrix.of (fun i j => I (fun x => x r * A x i j)))) (d (fun x => cfc k (A x)))) (fun a => t a / q a)) (fun a => ProbabilityTheory.gaussianPDFReal 0 1 a / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a))) (fun a => -Real.log (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a)))) (d A)) (fun F r x => Matrix.of (fun i j => fderiv ℝ (fun y => F y i j) x (PiLp.single 2 r (1 : ℝ))))) (fun F => ∀ i j, MeasureTheory.MemLp (fun x => F x i j) 2 γ)) (MeasureTheory.integral γ)) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  intro m hm A hA hAs hAb hAm hZ hK g hgs hg2
  have hcompact : (∀ a : ℝ, -6 ≤ a → a ≤ 10 → scalarCertificate k q a) ∧
      logarithmicGaps q := Submission.Entropy.two_eigenvalue_compact_certificate
  have hnegative : ∀ a : ℝ, a ≤ -6 → scalarCertificate k q a :=
    Submission.Entropy.two_eigenvalue_negative_certificate
  have hpositive : ∀ a : ℝ, 10 ≤ a → scalarCertificate k q a :=
    Submission.Entropy.two_eigenvalue_positive_certificate
  have hcert : ∀ a : ℝ, scalarCertificate k q a := by
    intro a
    by_cases hlo : a ≤ -6
    · exact hnegative a hlo
    by_cases hhi : 10 ≤ a
    · exact hpositive a hhi
    exact hcompact.1 a (le_of_not_ge hlo) (le_of_not_ge hhi)
  have hp : positiveWeight k := fun a => (hcert a).1
  have hscalar : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) k ∧ Continuous q ∧
      (∀ a : ℝ, 0 < q a) ∧ pairEstimate k q :=
    Submission.Entropy.two_eigenvalue_secant_deduction hcert hcompact.2
  let X : Fin m → Matrix (Fin m) (Fin m) ℝ := fun r =>
    Matrix.of (fun i j => MeasureTheory.integral
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))
      (fun x => x r * A x i j))
  have hX : ∀ r, (X r).IsHermitian := by
    intro r
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [X, Matrix.of_apply, star_trivial]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    congr 1
    simpa only [star_trivial] using (hA x).apply i j
  refine ⟨hp, ?_⟩
  exact Submission.Entropy.two_eigenvalue_matrix_bridge k q
    hscalar.1 hscalar.2.1 hscalar.2.2.1 hp hscalar.2.2.2
    m hm A hA X hX hAs hAb hZ hK g hgs hg2
