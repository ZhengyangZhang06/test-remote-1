import Mathlib
import ChallengeDeps
import Submission.Obl.Entropy__linear_transport_limit.Assembly
import Submission.Obl.Entropy__linear_transport_limit.Compactness
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.linear_transport_limit`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__linear_transport_limit`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__linear_transport_limit/`
belong to this obligation.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
open Submission.Obl.Entropy__linear_transport_limit

theorem Submission.Entropy.linear_transport_limit : ∀ m : ℕ, 1 ≤ m → ∀ q : ℝ → ℝ, (∀ U V : (Matrix (Fin m) (Fin m) ℝ), U.IsHermitian → V.IsHermitian → Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => ((cfc q U) i j - (cfc q V) i j) ^ 2)) ≤ Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (U i j - V i j) ^ 2))) → ∀ Fseq : ℕ → (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), ∀ Aseq : ℕ → (EuclideanSpace ℝ (Fin m)) → (Matrix (Fin m) (Fin m) ℝ), ∀ Xseq : ℕ → Fin m → (Matrix (Fin m) (Fin m) ℝ), (∀ n, ContDiff ℝ 1 (Fseq n) ∧ MeasureTheory.MemLp (Fseq n) 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) ∧ MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (Fseq n) = 0) → (∀ n, (∀ x, (Aseq n x).IsHermitian) ∧ (∀ i j, MeasureTheory.MemLp (fun x => Aseq n x i j) 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))))) → (∀ n r, (Xseq n r).IsHermitian) → (∀ n x v i, (fderiv ℝ (Fseq n) x v) i = Finset.sum Finset.univ (fun j : Fin m => (cfc q (Aseq n x)) i j * v j)) → (Filter.Tendsto (fun n => MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (fun x => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (Aseq n x i j - Finset.sum Finset.univ (fun r : Fin m => x r * Xseq n r i j)) ^ 2)))) Filter.atTop (nhds (0 : ℝ))) → (Filter.Tendsto (fun n => Finset.sum Finset.univ (fun r : Fin m => Xseq n r * Xseq n r)) Filter.atTop (nhds (1 : (Matrix (Fin m) (Fin m) ℝ)))) → ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ F : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), ∃ X : Fin m → (Matrix (Fin m) (Fin m) ℝ), (ContDiff ℝ 1 F) ∧ (MeasureTheory.MemLp F 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))) ∧ (MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (F) = 0) ∧ (∀ r, (X r).IsHermitian) ∧ (Finset.sum Finset.univ (fun r : Fin m => X r * X r) = (1 : (Matrix (Fin m) (Fin m) ℝ))) ∧ (∀ x v i, (fderiv ℝ (F) x v) i = Finset.sum Finset.univ (fun j : Fin m => (cfc q (Finset.sum Finset.univ (fun r : Fin m => x r • X r))) i j * v j)) ∧ (Filter.Tendsto (fun n => MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (fun x => ‖Fseq (σ n) x - F x‖ ^ 2)) Filter.atTop (nhds (0 : ℝ))) := by
  intro m hm q hq Fseq Aseq Xseq hF hA hXsym hderiv hrem hnorm
  obtain ⟨σ, hσ, X, hX, hXherm, hXnorm⟩ := normalized_coefficient_subsequence Xseq hXsym hnorm
  let J := fun x : E m => entriesCLM m (entries (cfc q (linearField X x)))
  have hDF : ∀ n, MemLp (fderiv ℝ (Fseq (σ n))) 2 (stdGaussian (E m)) := by
    intro n
    exact memLp_fderiv_of_field hq (hF (σ n)).1 (hA (σ n)).1 (hA (σ n)).2
      (hderiv (σ n))
  have hJ := jacobian_limit hq (fun n => (hF (σ n)).1) (fun n => hA (σ n))
    (fun n => hderiv (σ n)) (hrem.comp hσ.tendsto_atTop) hX hXherm
  obtain ⟨G, hG, hGmem, hGmean, hDG, hGlim⟩ :=
    centered_C1_limit (fun n => Fseq (σ n)) J (fun n => hF (σ n)) hDF
      hJ.1 hJ.2.1 hJ.2.2
  refine ⟨σ, hσ, G, X, hG, hGmem, hGmean, hXherm, hXnorm, ?_, hGlim⟩
  intro x v i
  rw [hDG x]
  rfl
