import Mathlib
import ChallengeDeps
import Submission.Obl.Entropy__affine_limit_density.Assembly
import Submission.Obl.Entropy__affine_limit_density.PullbackProduct
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.affine_limit_density`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__affine_limit_density`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__affine_limit_density/`
belong to this obligation.
-/

namespace Submission.Obl.Entropy__affine_limit_density

theorem _root_.Submission.Entropy.affine_limit_density : ∀ m : ℕ, 1 ≤ m → ∀ f : (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ x, 0 ≤ f x) → MeasureTheory.Integrable f (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) → MeasureTheory.integral (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) (f) = 1 → MeasureTheory.Integrable (fun x => f x * ‖x‖ ^ 2) (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) → ∀ b : (EuclideanSpace ℝ (Fin m)), b = MeasureTheory.integral (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) (fun x => f x • x) → ∀ C : (Matrix (Fin m) (Fin m) ℝ), C = (fun i j => MeasureTheory.integral (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) (fun x => f x * (x i - b i) * (x j - b j))) → C.PosDef → ∀ fseq : ℕ → (EuclideanSpace ℝ (Fin m)) → ℝ, ∀ bseq : ℕ → (EuclideanSpace ℝ (Fin m)), ∀ Cseq : ℕ → (Matrix (Fin m) (Fin m) ℝ), ∀ Pseq : ℕ → (EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin m)), ∀ Fseq : ℕ → (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), (∀ n, (∀ x, 0 ≤ fseq n x) ∧ MeasureTheory.Integrable (fseq n) (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) ∧ MeasureTheory.integral (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) (fseq n) = 1 ∧ MeasureTheory.Integrable (fun x => fseq n x * ‖x‖ ^ 2) (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) ∧ bseq n = MeasureTheory.integral (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) (fun x => (fseq n) x • x) ∧ Cseq n = (fun i j => MeasureTheory.integral (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) (fun x => (fseq n) x * (x i - (bseq n) i) * (x j - (bseq n) j)))) → (Filter.Tendsto (fun n => MeasureTheory.integral (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) (fun x => |fseq n x - f x|)) Filter.atTop (nhds (0 : ℝ))) → (Filter.Tendsto (bseq) Filter.atTop (nhds (b))) → (Filter.Tendsto (Cseq) Filter.atTop (nhds (C))) → (∀ n, MeasureTheory.Measure.map (Fseq n) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) = MeasureTheory.Measure.map (fun x => Pseq n (x - bseq n)) ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))).withDensity (fun x => ENNReal.ofReal (fseq n x)))) → (∀ n, ContDiff ℝ 1 (Fseq n) ∧ MeasureTheory.MemLp (Fseq n) 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) ∧ MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (Fseq n) = 0) → ∀ σ : ℕ → ℕ, StrictMono σ → ∀ F : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), MeasureTheory.MemLp F 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) → MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (F) = 0 → (Filter.Tendsto (fun n => MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (fun x => ‖Fseq (σ n) x - F x‖ ^ 2)) Filter.atTop (nhds (0 : ℝ))) → (∃ L : (EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin m)), ∃ a : (EuclideanSpace ℝ (Fin m)), MeasureTheory.Measure.map F (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))).withDensity (fun x => ENNReal.ofReal (|LinearMap.det L.toLinearMap|⁻¹ * (if ∀ i : Fin m, 0 ≤ L.symm (x - a) i then Real.exp (-Finset.sum Finset.univ (fun i : Fin m => L.symm (x - a) i)) else 0)))) → ((fun i j => MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (fun x => F x i * F x j)) = (1 : (Matrix (Fin m) (Fin m) ℝ))) → ∃ L : (EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin m)), ∃ a : (EuclideanSpace ℝ (Fin m)), ∀ᵐ x ∂MeasureTheory.volume, f x = |LinearMap.det L.toLinearMap|⁻¹ * (if ∀ i : Fin m, 0 ≤ L.symm (x - a) i then Real.exp (-Finset.sum Finset.univ (fun i : Fin m => L.symm (x - a) i)) else 0) := by
  intro m hm f hf0 hf hmass hf2 b hb C hCdef hC fseq bseq Cseq Pseq Fseq
    hseq hL1 hbseq hCseq hlaw hFseq σ hσ F hF hFmean hL2 hprod hFcov
  have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  obtain ⟨P, hP⟩ := exists_affine_limit_law hf0 hf
    (fun n => (hseq (σ n)).1) (fun n => (hseq (σ n)).2.1)
    (fun n => (hseq (σ n)).2.2.2.1) (hbseq.comp hσ.tendsto_atTop)
    (fun n => (hseq (σ n)).2.2.2.2.2) hC (hCseq.comp hσ.tendsto_atTop)
    (fun n => (hFseq (σ n)).2.1) hF hL2 (hL1.comp hσ.tendsto_atTop)
    (fun n => hlaw (σ n)) hFcov
  obtain ⟨L, a, hprod⟩ := hprod
  exact exists_affine_exponential_of_map_eq hf0 hf P b L a (hP.symm.trans hprod)

end Submission.Obl.Entropy__affine_limit_density
