import Mathlib

set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.Entropy__gaussian_l2_poincare

open MeasureTheory

/-- Cauchy--Schwarz against the constant function, in a form without square roots. -/
theorem integral_sq_le_mass_mul_integral_sq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {g : α → ℝ}
    (hg : Integrable g μ) (hg2 : Integrable (fun x => g x ^ 2) μ) :
    (∫ x, g x ∂μ) ^ 2 ≤ μ.real Set.univ * ∫ x, g x ^ 2 ∂μ := by
  let M := μ.real Set.univ
  let I := ∫ x, g x ∂μ
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  by_cases hzero : M = 0
  · have hz : μ = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      simpa [M, measureReal_def, ENNReal.toReal_eq_zero_iff] using hzero
    simp [hz]
  have hpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hzero)
  have hnonneg : 0 ≤ ∫ x, (M * g x - I) ^ 2 ∂μ :=
    integral_nonneg (fun x => sq_nonneg _)
  have heq : (∫ x, (M * g x - I) ^ 2 ∂μ) =
      M ^ 2 * (∫ x, g x ^ 2 ∂μ) - M * I ^ 2 := by
    calc
      _ = ∫ x, M ^ 2 * g x ^ 2 - (2 * M * I) * g x + I ^ 2 ∂μ := by
        congr 1
        funext x
        ring
      _ = _ := by
        erw [integral_add ((hg2.const_mul (M ^ 2)).sub (hg.const_mul (2 * M * I)))
          (integrable_const (I ^ 2)),
          integral_sub (hg2.const_mul (M ^ 2)) (hg.const_mul (2 * M * I)), integral_const_mul,
          integral_const_mul, integral_const]
        change M ^ 2 * (∫ x, g x ^ 2 ∂μ) - 2 * M * I * I + M * I ^ 2 = _
        ring
  rw [heq] at hnonneg
  nlinarith

/-- The squared norm of a Bochner integral is controlled by its second moment. -/
theorem norm_integral_sq_le_mass_mul_integral_norm_sq {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) [IsFiniteMeasure μ] {g : α → E}
    (hg : Integrable g μ) (hg2 : Integrable (fun x => ‖g x‖ ^ 2) μ) :
    ‖∫ x, g x ∂μ‖ ^ 2 ≤ μ.real Set.univ * ∫ x, ‖g x‖ ^ 2 ∂μ := by
  calc
    _ ≤ (∫ x, ‖g x‖ ∂μ) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm _) 2
    _ ≤ _ := integral_sq_le_mass_mul_integral_sq μ hg.norm hg2

end Submission.Obl.Entropy__gaussian_l2_poincare
