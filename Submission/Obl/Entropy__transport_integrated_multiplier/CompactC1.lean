import Submission.Obl.Entropy__continuous_jacobian_of_l2_limit.Mollifier

open MeasureTheory Filter Set ContinuousLinearMap
open scoped Topology ContDiff BigOperators Convolution

namespace Submission.Obl.Entropy__transport_integrated_multiplier

open Submission.Obl.Entropy__continuous_jacobian_of_l2_limit

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

private noncomputable def shrinkingBump (n : ℕ) : ContDiffBump (0 : E) where
  rIn := ((n : ℝ) + 1)⁻¹ / 2
  rOut := ((n : ℝ) + 1)⁻¹
  rIn_pos := by positivity
  rIn_lt_rOut := by apply half_lt_self; positivity

private lemma shrinkingBump_tendsto :
    Tendsto (fun n => (shrinkingBump (m := m) n).rOut) atTop (𝓝 0) := by
  simpa only [shrinkingBump, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Averaging against a normalized bump preserves a global norm bound. -/
lemma norm_mollify_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (φ : ContDiffBump (0 : E)) {f : E → F} {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (x : E) : ‖mollify φ f x‖ ≤ C := by
  have h := norm_integral_le_of_norm_le (φ.integrable_normed (μ := volume) |>.mul_const C)
    (ae_of_all _ fun y => show ‖φ.normed volume y • f (x-y)‖ ≤ φ.normed volume y * C from by
      rw [norm_smul, Real.norm_of_nonneg (φ.nonneg_normed y)]
      exact mul_le_mul_of_nonneg_left (hC _) (φ.nonneg_normed y))
  change ‖∫ y, φ.normed volume y • f (x-y)‖ ≤ C
  simpa only [integral_mul_const, φ.integral_normed, one_mul] using h

/-- Compact C1 functions can test an L1 weak derivative identity. -/
theorem compact_c1_test_of_smooth
    {ι : Type*} [Fintype ι] (v : ι → E) {μ : Measure E}
    {f : E → ℝ} {b : ι → E → ℝ}
    (hf : Integrable f μ) (hb : ∀ r, Integrable (b r) μ)
    (hweak : ∀ z : E → ℝ, ContDiff ℝ ∞ z → HasCompactSupport z →
      (∫ x, z x * f x ∂μ) = -∑ r, ∫ x, fderiv ℝ z x (v r) * b r x ∂μ)
    {p : E → ℝ} (hp : ContDiff ℝ 1 p) (hpc : HasCompactSupport p) :
    (∫ x, p x * f x ∂μ) = -∑ r, ∫ x, fderiv ℝ p x (v r) * b r x ∂μ := by
  let z : ℕ → E → ℝ := fun n => mollify (shrinkingBump n) p
  have hz (n : ℕ) : ContDiff ℝ ∞ (z n) :=
    Submission.Obl.Entropy__mollified_convex_sequence.smooth_contDiff _ hp.continuous
  have hzc (n : ℕ) : HasCompactSupport (z n) :=
    (shrinkingBump n).hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hpc
  have hzd (n : ℕ) (x : E) : fderiv ℝ (z n) x =
      mollify (shrinkingBump n) (fderiv ℝ p) x :=
    (mollify_hasFDerivAt _ hp x).fderiv
  obtain ⟨C, hC⟩ := hp.continuous.norm.bddAbove_range_of_hasCompactSupport
    (hpc.comp_left norm_zero)
  have hCb (x : E) : ‖p x‖ ≤ C := hC (mem_range_self x)
  obtain ⟨D, hD⟩ := (hp.continuous_fderiv one_ne_zero).norm.bddAbove_range_of_hasCompactSupport
    ((hpc.fderiv ℝ).comp_left norm_zero)
  have hDb (x : E) : ‖fderiv ℝ p x‖ ≤ D := hD (mem_range_self x)
  have hleft : Tendsto (fun n => ∫ x, z n x * f x ∂μ) atTop (𝓝 (∫ x, p x * f x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => C * ‖f x‖)
    · intro n
      exact (hz n).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable
    · exact hf.norm.const_mul C
    · intro n
      exact ae_of_all _ fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (norm_mollify_le _ hCb x) (norm_nonneg _)
    · exact ae_of_all _ fun x =>
        (ContDiffBump.convolution_tendsto_right_of_continuous shrinkingBump_tendsto
          hp.continuous x).mul_const (f x)
  have hright (r : ι) : Tendsto (fun n => ∫ x, fderiv ℝ (z n) x (v r) * b r x ∂μ)
      atTop (𝓝 (∫ x, fderiv ℝ p x (v r) * b r x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => (D * ‖v r‖) * ‖b r x‖)
    · intro n
      exact (((hz n).continuous_fderiv (by simp)).eval_const _).aestronglyMeasurable.mul
        (hb r).aestronglyMeasurable
    · exact (hb r).norm.const_mul _
    · intro n
      exact ae_of_all _ fun x => by
        rw [norm_mul, hzd]
        gcongr
        exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
          (norm_mollify_le _ hDb x) (norm_nonneg _))
    · exact ae_of_all _ fun x => by
        simp only [hzd]
        exact ((ContDiffBump.convolution_tendsto_right_of_continuous shrinkingBump_tendsto
          (hp.continuous_fderiv one_ne_zero) x).eval_const (v r)).mul_const (b r x)
  have hs := (tendsto_finsetSum Finset.univ fun r _ => hright r).neg
  exact tendsto_nhds_unique hleft (hs.congr' (Eventually.of_forall fun n =>
    (hweak (z n) (hz n) (hzc n)).symm))

end Submission.Obl.Entropy__transport_integrated_multiplier
