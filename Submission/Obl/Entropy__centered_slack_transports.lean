import Mathlib
import ChallengeDeps
import Submission.Obl.Entropy__centered_slack_transports.Fields
import Submission.Obl.Entropy__centered_slack_transports.Transport
import Submission.Obl.Entropy__centered_slack_transports.Spectrum
import Submission.Obl.Entropy__centered_slack_transports.Slack
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.centered_slack_transports`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__centered_slack_transports`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__centered_slack_transports/`
belong to this obligation.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators
open Submission.Obl.Entropy__centered_slack_transports
open Submission.Lib.EntropyTools

theorem Submission.Entropy.centered_slack_transports : ∀ m : ℕ, 1 ≤ m → (fun (q : ℝ → ℝ) (γ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) (ω : ℝ → ℝ) => ∀ f : ℕ → (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ n, (∀ x, 0 ≤ f n x) ∧ MeasureTheory.Integrable (f n) MeasureTheory.volume ∧ MeasureTheory.integral MeasureTheory.volume (f n) = 1 ∧ MeasureTheory.Integrable (fun x => f n x * ‖x‖ ^ 2) MeasureTheory.volume) → ∀ P : ℕ → (EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin m)), ∀ G : ℕ → (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), ∀ A : ℕ → (EuclideanSpace ℝ (Fin m)) → (Matrix (Fin m) (Fin m) ℝ), (∀ n, ContDiff ℝ 1 (G n)) → (∀ n i j, Continuous (fun x => A n x i j)) → (∀ n x, (A n x).IsHermitian) → (∀ n, ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A n x i j| ≤ R) → (∀ n x i j, cfc q (A n x) i j = (fderiv ℝ (G n) x (PiLp.single 2 j (1 : ℝ))) i) → (∀ n, MeasureTheory.Measure.map (G n) γ = MeasureTheory.Measure.withDensity MeasureTheory.volume (fun x => ENNReal.ofReal (|LinearMap.det (P n).toLinearMap|⁻¹ * f n ((P n).symm x)))) → (fun (X : ℕ → Fin m → (Matrix (Fin m) (Fin m) ℝ)) => (fun (B : ℕ → (Matrix (Fin m) (Fin m) ℝ)) => (fun (energy : ℕ → ℝ) => ∀ hB : ∀ n, (B n).PosSemidef, ∀ δ : ℕ → ℝ, Filter.Tendsto (δ) Filter.atTop (nhds (0)) → (∀ n, energy n / 500 + Finset.sum Finset.univ (fun i : Fin m => ω ((hB n).isHermitian.eigenvalues i)) / 1000 ≤ δ n) → ∃ F : ℕ → (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), (∀ n, ContDiff ℝ 1 (F n) ∧ MeasureTheory.MemLp (F n) 2 γ ∧ MeasureTheory.integral γ (F n) = 0) ∧ (∀ n, MeasureTheory.Measure.map (F n) γ = MeasureTheory.Measure.map (fun x => P n (x - MeasureTheory.integral MeasureTheory.volume (fun y => f n y • y))) (MeasureTheory.Measure.withDensity MeasureTheory.volume (fun x => ENNReal.ofReal (f n x)))) ∧ (∀ n i j, MeasureTheory.MemLp (fun x => A n x i j) 2 γ) ∧ (∀ n r, (X n r).IsHermitian) ∧ (∀ n x v i, (fderiv ℝ (F n) x v) i = Finset.sum Finset.univ (fun j : Fin m => cfc q (A n x) i j * v j)) ∧ Filter.Tendsto (energy) Filter.atTop (nhds (0)) ∧ Filter.Tendsto (B) Filter.atTop (nhds (1 : (Matrix (Fin m) (Fin m) ℝ)))) (fun n => MeasureTheory.integral γ (fun x => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => ((A n x - Finset.sum Finset.univ (fun r : Fin m => x r • X n r)) i j) ^ 2))))) (fun n => Finset.sum Finset.univ (fun r : Fin m => X n r * X n r))) (fun n r => Matrix.of (fun i j => MeasureTheory.integral γ (fun x => x r * A n x i j)))) (fun t : ℝ => ProbabilityTheory.gaussianPDFReal 0 1 t / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-t)) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (fun z : ℝ => (3 * (z - 1) ^ 2 / (37 + 3 * z)) * ((3 : ℝ) / 20 + ((49 : ℝ) / 100) * (37 / (37 + 3 * z))) * (if z = 0 then (13 : ℝ) / 100 else min ((13 : ℝ) / 100) (32 / (25 * Real.sqrt z)))) := by
  classical
  intro m hm f hf P G A hG hAc hAh hAb hD hLaw hB δ hδ hbound
  let γ := stdGaussian (EuclideanSpace ℝ (Fin m))
  let X := fun n r => Matrix.of (fun i j => ∫ x, x r * A n x i j ∂γ)
  let B := fun n => ∑ r, X n r * X n r
  let energy := fun n => ∫ x, ∑ i, ∑ j,
    ((A n x - ∑ r, x r • X n r) i j) ^ 2 ∂γ
  change ∀ n, (B n).PosSemidef at hB
  change ∀ n, energy n / 500 +
    (∑ i, rigidityWeight ((hB n).isHermitian.eigenvalues i)) / 1000 ≤ δ n at hbound
  have henergy (n : ℕ) : 0 ≤ energy n := by
    apply integral_nonneg
    intro x
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hlimits := vanish_of_slack energy δ (fun n => (hB n).isHermitian.eigenvalues)
    henergy (fun n i => (hB n).eigenvalues_nonneg i) hδ hbound
  have hmatrix : Tendsto B atTop (nhds 1) :=
    tendsto_matrix_one_of_eigenvalues B (fun n => (hB n).isHermitian)
      (eigenvalue_limits_of_weight _ (fun n i => (hB n).eigenvalues_nonneg i) hlimits.2)
  have hcenter (n : ℕ) := center_transport (hf n).1 (hf n).2.1 (hf n).2.2.2
    (P n) (G n) (hG n) ((hLaw n).trans (map_linear_density (P n) (f n)).symm)
  choose F hF hFlaw hFderiv using hcenter
  refine ⟨F, hF, hFlaw, ?_, ?_, ?_, hlimits.1, hmatrix⟩
  · intro n i j
    exact field_memLp (hAc n) (hAb n) i j
  · intro n r
    exact coefficient_isHermitian (A n) (hAh n) r
  · intro n x v i
    rw [hFderiv n x]
    exact derivative_from_basis (G n) _ (hD n) x v i
