import Submission.Obl.Entropy__transport_finite_jacobian_energy.Hessian

set_option autoImplicit false

open Filter MeasureTheory
open scoped BigOperators ContDiff Topology

namespace Submission.Obl.Entropy__transport_finite_jacobian_energy

variable {m : ℕ}

lemma exists_energy_cutoffs :
    ∃ (χ : ℕ → space m → ℝ) (D : ℝ), 0 ≤ D ∧
      (∀ n, ContDiff ℝ ∞ (χ n) ∧ HasCompactSupport (χ n)) ∧
      (∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1) ∧
      (∀ n x i, |directional (basisVector i) (χ n) x| ≤ D) ∧
      (∀ x, Tendsto (fun n => χ n x) atTop (𝓝 1)) := by
  let b : ContDiffBump (0 : space m) := ⟨1, 2, by norm_num, by norm_num⟩
  obtain ⟨C, hC⟩ := b.hasCompactSupport.fderiv ℝ |>.exists_bound_of_continuous
    (b.contDiff.continuous_fderiv (by simp : (∞ : WithTop ℕ∞) ≠ 0))
  let χ (n : ℕ) (x : space m) := b (((n : ℝ) + 1)⁻¹ • x)
  have hn (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity
  have hc (n : ℕ) : ContDiff ℝ ∞ (χ n) :=
    b.contDiff.comp (contDiff_const.fun_smul contDiff_id)
  refine ⟨χ, max C 0, le_max_right _ _, ?_, ?_, ?_, ?_⟩
  · intro n
    refine ⟨hc n, ?_⟩
    apply HasCompactSupport.intro (isCompact_closedBall (0 : space m) (2 * ((n : ℝ) + 1)))
    intro x hx
    apply b.zero_of_le_dist
    change 2 ≤ dist (((n : ℝ) + 1)⁻¹ • x) 0
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hn n))]
    apply (le_of_lt ?_)
    apply (lt_inv_mul_iff₀ (hn n)).mpr
    simpa [Metric.mem_closedBall, dist_zero_right, mul_comm] using hx
  · intro n x
    exact ⟨b.nonneg, b.le_one⟩
  · intro n x i
    have hd : DifferentiableAt ℝ b (((n : ℝ) + 1)⁻¹ • x) :=
      (show ContDiff ℝ ∞ (fun y : space m => b y) from b.contDiff).differentiable (by simp) _
    have he : directional (basisVector i) (χ n) x =
        ((n : ℝ) + 1)⁻¹ *
          fderiv ℝ b (((n : ℝ) + 1)⁻¹ • x) (basisVector i) := by
      dsimp [directional, χ]
      erw [fderiv_comp x hd (show DifferentiableAt ℝ (fun y : space m => ((n : ℝ) + 1)⁻¹ • y) x from
        (contDiff_const.fun_smul (contDiff_id : ContDiff ℝ ∞ (id : space m → space m))).differentiable (by simp) x)]
      change (fderiv ℝ b (((n : ℝ) + 1)⁻¹ • x))
        (fderiv ℝ (fun y : space m => ((n : ℝ) + 1)⁻¹ • y) x (basisVector i)) = _
      rw [show fderiv ℝ (fun y : space m => ((n : ℝ) + 1)⁻¹ • y) x =
        ((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ (space m) from
          (hasFDerivAt_id x).const_smul ((n : ℝ) + 1)⁻¹ |>.fderiv]
      simp [map_smul]
    rw [he, abs_mul, abs_of_pos (inv_pos.mpr (hn n))]
    have hv : ‖basisVector i‖ = (1 : ℝ) := by simp [basisVector]
    have hb := (fderiv ℝ b (((n : ℝ) + 1)⁻¹ • x)).le_opNorm (basisVector i)
    rw [hv, mul_one, Real.norm_eq_abs] at hb
    have hscale : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact le_add_of_nonneg_left (Nat.cast_nonneg n))
    calc
      _ ≤ |fderiv ℝ b (((n : ℝ) + 1)⁻¹ • x) (basisVector i)| :=
        mul_le_of_le_one_left (abs_nonneg _) hscale
      _ ≤ C := hb.trans (hC _)
      _ ≤ max C 0 := le_max_left _ _
  · intro x
    have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • x) atTop (𝓝 (0 : space m)) := by
      have hscalar : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
      simpa using hscalar.smul_const x
    simpa [χ, Function.comp_def, b.one_of_mem_closedBall (by simp [b] : (0 : space m) ∈ Metric.closedBall 0 b.rIn)]
      using b.continuous.continuousAt.tendsto.comp ht

end Submission.Obl.Entropy__transport_finite_jacobian_energy
