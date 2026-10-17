import Mathlib
import ChallengeDeps
import Submission.Obl.Entropy__gaussian_l2_poincare.CoordinatePoincare

open MeasureTheory ProbabilityTheory

/-- A finite Gaussian Poincare constant follows from rotation of two independent copies. -/
theorem Submission.Entropy.gaussian_l2_poincare : ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ F : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), ContDiff ℝ 1 F → MeasureTheory.MemLp F 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) → MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) F = 0 → MeasureTheory.MemLp (fderiv ℝ F) 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) → MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (fun x => ‖F x‖ ^ 2) ≤ C * MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (fun x => ‖fderiv ℝ F x‖ ^ 2) := by
  intro m
  let K := (Real.pi / 2) ^ 2 * ∫ x : EuclideanSpace ℝ (Fin m), ‖x‖ ^ 2
    ∂stdGaussian (EuclideanSpace ℝ (Fin m))
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) (integral_nonneg (fun x => sq_nonneg _))
  refine ⟨K + 1, by positivity, ?_⟩
  intro F hF hmem hm hD
  have hp := Submission.Obl.Entropy__gaussian_l2_poincare.gaussian_poincare_finite
    hF integral_id_stdGaussian hmem hm (hD.integrable_norm_pow (by norm_num))
  apply hp.trans
  exact mul_le_mul_of_nonneg_right (show K ≤ K + 1 by linarith)
    (integral_nonneg (fun x => sq_nonneg _))
