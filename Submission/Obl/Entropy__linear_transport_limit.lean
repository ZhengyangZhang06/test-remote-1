import Mathlib
import ChallengeDeps
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.linear_transport_limit`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__linear_transport_limit`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__linear_transport_limit/`
belong to this obligation.
-/

theorem Submission.Entropy.linear_transport_limit : ∀ m : ℕ, 1 ≤ m → ∀ q : ℝ → ℝ, (∀ U V : (Matrix (Fin m) (Fin m) ℝ), U.IsHermitian → V.IsHermitian → Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => ((cfc q U) i j - (cfc q V) i j) ^ 2)) ≤ Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (U i j - V i j) ^ 2))) → ∀ Fseq : ℕ → (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), ∀ Aseq : ℕ → (EuclideanSpace ℝ (Fin m)) → (Matrix (Fin m) (Fin m) ℝ), ∀ Xseq : ℕ → Fin m → (Matrix (Fin m) (Fin m) ℝ), (∀ n, ContDiff ℝ 1 (Fseq n) ∧ MeasureTheory.MemLp (Fseq n) 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) ∧ MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (Fseq n) = 0) → (∀ n, (∀ x, (Aseq n x).IsHermitian) ∧ (∀ i j, MeasureTheory.MemLp (fun x => Aseq n x i j) 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))))) → (∀ n r, (Xseq n r).IsHermitian) → (∀ n x v i, (fderiv ℝ (Fseq n) x v) i = Finset.sum Finset.univ (fun j : Fin m => (cfc q (Aseq n x)) i j * v j)) → (Filter.Tendsto (fun n => MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (fun x => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (Aseq n x i j - Finset.sum Finset.univ (fun r : Fin m => x r * Xseq n r i j)) ^ 2)))) Filter.atTop (nhds (0 : ℝ))) → (Filter.Tendsto (fun n => Finset.sum Finset.univ (fun r : Fin m => Xseq n r * Xseq n r)) Filter.atTop (nhds (1 : (Matrix (Fin m) (Fin m) ℝ)))) → ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ F : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), ∃ X : Fin m → (Matrix (Fin m) (Fin m) ℝ), (ContDiff ℝ 1 F) ∧ (MeasureTheory.MemLp F 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))) ∧ (MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (F) = 0) ∧ (∀ r, (X r).IsHermitian) ∧ (Finset.sum Finset.univ (fun r : Fin m => X r * X r) = (1 : (Matrix (Fin m) (Fin m) ℝ))) ∧ (∀ x v i, (fderiv ℝ (F) x v) i = Finset.sum Finset.univ (fun j : Fin m => (cfc q (Finset.sum Finset.univ (fun r : Fin m => x r • X r))) i j * v j)) ∧ (Filter.Tendsto (fun n => MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (fun x => ‖Fseq (σ n) x - F x‖ ^ 2)) Filter.atTop (nhds (0 : ℝ))) := by
  sorry
