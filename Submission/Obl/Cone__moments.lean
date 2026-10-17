import Submission.Obl.Cone__moments.Covariance

open Submission.Obl.Cone__moments Submission.Lib.Cone
set_option linter.unusedVariables false

/-!
# `Submission.Cone.moments`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Cone__moments`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Cone__moments/`
belong to this obligation.
-/

theorem Submission.Cone.moments : ∀ n : ℕ, 1 ≤ n → ∀ K : Set (EuclideanSpace ℝ (Fin n)), SimplexIsotropic.IsConvexBody K → ∀ f : (EuclideanSpace ℝ (Fin (n + 1))) → ℝ, f = Set.indicator {z | 0 ≤ z 0 ∧ ∃ x ∈ K, ∀ i : Fin n, z i.succ = z 0 * x i} (fun z => Real.exp (-z 0) / ((n.factorial : ℝ) * SimplexIsotropic.vol K)) → ∀ b : (EuclideanSpace ℝ (Fin (n + 1))), b = MeasureTheory.integral MeasureTheory.volume (fun x => f x • x) → ∀ C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, C = (fun i j => MeasureTheory.integral MeasureTheory.volume (fun x => f x * (x i - b i) * (x j - b j))) → ∀ H : ℝ, H = -MeasureTheory.integral MeasureTheory.volume (fun x => f x * Real.log (f x)) → 0 < SimplexIsotropic.vol K ∧ 0 < (SimplexIsotropic.covMatrix K).det ∧ (∀ x, 0 ≤ f x) ∧ UpperSemicontinuous f ∧ ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) ∧ MeasureTheory.Integrable f MeasureTheory.volume ∧ MeasureTheory.integral MeasureTheory.volume f = 1 ∧ MeasureTheory.Integrable (fun x => f x * ‖x‖ ^ 2) MeasureTheory.volume ∧ MeasureTheory.Integrable (fun x => f x * Real.log (f x)) MeasureTheory.volume ∧ H = (n : ℝ) + 1 + Real.log ((n.factorial : ℝ) * SimplexIsotropic.vol K) ∧ C.det = ((n : ℝ) + 1) ^ (n + 1) * ((n : ℝ) + 2) ^ n * (SimplexIsotropic.covMatrix K).det := by
  intro n hn K hK f hf b hb C hC H hH
  change f = density K at hf
  subst f
  have hb' : b = ((n : ℝ)+1) • join 1 (SimplexIsotropic.centroid K) :=
    hb.trans (density_mean hK)
  have hC' : C = coneCov K := by
    rw [hC, hb']
    rfl
  refine ⟨Submission.Lib.ConvexBody.body_vol_pos hK,
    Submission.Lib.ConvexBody.body_covMatrix_det_pos hK,
    density_nonneg hK, density_upperSemicontinuous hK, density_log_concave hK,
    density_integrable hK, density_integral hK, density_norm_sq_integrable hK,
    density_entropy_integrable hK, ?_, ?_⟩
  · rw [hH]
    exact density_entropy hK
  · rw [hC']
    exact coneCov_det hK
