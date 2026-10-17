import Submission.Obl.Entropy__gaussian_l2_poincare.IntegralSquare

set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.Entropy__gaussian_l2_poincare

open MeasureTheory Set
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The energy of a derivative along the circular interpolation of two points. -/
noncomputable def rotationEnergy (f : E → F) (t : ℝ) (p : E × E) : ℝ :=
  ‖fderiv ℝ f (Real.cos t • p.1 + Real.sin t • p.2)‖ ^ 2 *
    ‖(-Real.sin t) • p.1 + Real.cos t • p.2‖ ^ 2

/-- Circular interpolation controls the squared difference by its derivative energy. -/
theorem norm_sub_sq_le_rotationEnergy {f : E → F} (hf : ContDiff ℝ 1 f) (x y : E) :
    ‖f y - f x‖ ^ 2 ≤ (Real.pi / 2) *
      ∫ t in 0..Real.pi / 2, rotationEnergy f t (x, y) := by
  let u : ℝ → E := fun t => Real.cos t • x + Real.sin t • y
  let v : ℝ → E := fun t => (-Real.sin t) • x + Real.cos t • y
  let g : ℝ → F := fun t => fderiv ℝ f (u t) (v t)
  have hu (t : ℝ) : HasDerivAt u (v t) t :=
    ((Real.hasDerivAt_cos t).smul_const x).add ((Real.hasDerivAt_sin t).smul_const y)
  have hfg (t : ℝ) : HasDerivAt (fun t => f (u t)) (g t) t :=
    ((hf.differentiable (by norm_num)) (u t)).hasFDerivAt.comp_hasDerivAt t (hu t)
  have hc : Continuous g := (hf.continuous_fderiv (by norm_num)).comp
    (by dsimp [u]; fun_prop) |>.clm_apply (by dsimp [v]; fun_prop)
  have hec : Continuous (fun t => rotationEnergy f t (x, y)) := by
    unfold rotationEnergy
    exact (((hf.continuous_fderiv (by norm_num)).comp (by fun_prop)).norm.pow 2).mul
      ((by fun_prop : Continuous (fun t : ℝ => (-Real.sin t) • x + Real.cos t • y)).norm.pow 2)
  have hpi : 0 ≤ Real.pi / 2 := by positivity
  have heq : (∫ t in 0..Real.pi / 2, g t) = f y - f x := by
    simpa [u] using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hfg t) (hc.intervalIntegrable 0 (Real.pi / 2))
  rw [← heq, intervalIntegral.integral_of_le hpi]
  have hcs := norm_integral_sq_le_mass_mul_integral_norm_sq
    (volume.restrict (Ioc 0 (Real.pi / 2)))
    (hc.intervalIntegrable 0 (Real.pi / 2)).1 ((hc.norm.pow 2).intervalIntegrable 0 (Real.pi / 2)).1
  have hmass : (volume.restrict (Ioc 0 (Real.pi / 2))).real Set.univ = Real.pi / 2 := by
    simp [Measure.real, hpi]
  rw [hmass] at hcs
  refine hcs.trans (mul_le_mul_of_nonneg_left ?_ hpi)
  rw [intervalIntegral.integral_of_le hpi]
  apply integral_mono ((hc.norm.pow 2).intervalIntegrable 0 (Real.pi / 2)).1 (hec.intervalIntegrable 0 (Real.pi / 2)).1
  intro t
  change ‖(fderiv ℝ f (u t)) (v t)‖ ^ 2 ≤ ‖fderiv ℝ f (u t)‖ ^ 2 * ‖v t‖ ^ 2
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.le_opNorm _ _) 2

end Submission.Obl.Entropy__gaussian_l2_poincare
