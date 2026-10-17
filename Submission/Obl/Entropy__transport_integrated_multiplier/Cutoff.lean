import Mathlib

open MeasureTheory Filter Set
open scoped Topology ContDiff

namespace Submission.Obl.Entropy__transport_integrated_multiplier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private def baseBump : ContDiffBump (0 : E) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- Smooth compact cutoffs obtained by dilating a fixed bump. -/
noncomputable def cutoff (n : ℕ) (x : E) : ℝ :=
  (baseBump (E := E)) (((n : ℝ) + 1)⁻¹ • x)

lemma cutoff_contDiff (n : ℕ) : ContDiff ℝ ∞ (cutoff (E := E) n) :=
  (baseBump (E := E)).contDiff.comp (contDiff_const.smul contDiff_id)

lemma cutoff_hasCompactSupport (n : ℕ) : HasCompactSupport (cutoff (E := E) n) := by
  exact (baseBump (E := E)).hasCompactSupport.comp_homeomorph
    (Homeomorph.smulOfNeZero (((n : ℝ) + 1)⁻¹) (by positivity))

lemma cutoff_mem_Icc (n : ℕ) (x : E) : cutoff n x ∈ Icc (0 : ℝ) 1 :=
  ⟨(baseBump (E := E)).nonneg, (baseBump (E := E)).le_one⟩

lemma cutoff_tendsto (x : E) : Tendsto (fun n => cutoff n x) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hb : (baseBump (E := E)) (0 : E) = 1 :=
    (baseBump (E := E)).one_of_mem_closedBall (by simp [baseBump])
  simpa only [cutoff, Function.comp_def, zero_smul, hb] using
    (baseBump (E := E)).continuous.continuousAt.tendsto.comp (h.smul_const x)

lemma fderiv_cutoff (n : ℕ) (x v : E) :
    fderiv ℝ (cutoff n) x v =
      ((n : ℝ) + 1)⁻¹ *
        fderiv ℝ (baseBump (E := E)) (((n : ℝ) + 1)⁻¹ • x) v := by
  have h := (baseBump (E := E)).contDiff.differentiable (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hd := (h (((n : ℝ) + 1)⁻¹ • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul (((n : ℝ) + 1)⁻¹))
  unfold cutoff
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] using congrArg (fun L => L v) hd.fderiv

lemma fderiv_cutoff_tendsto (x v : E) :
    Tendsto (fun n => fderiv ℝ (cutoff n) x v) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hc := ((baseBump (E := E)).contDiff (n := (⊤ : ℕ∞))).continuous_fderiv (by simp)
  have hd := (hc.eval_const v).continuousAt.tendsto.comp (h.smul_const x)
  simpa only [fderiv_cutoff, Function.comp_def, zero_mul] using h.mul hd

lemma exists_bound_fderiv_cutoff :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n (x v : E), ‖fderiv ℝ (cutoff n) x v‖ ≤ C * ‖v‖ := by
  have hc := ((baseBump (E := E)).contDiff (n := (⊤ : ℕ∞))).continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := hc.norm.bddAbove_range_of_hasCompactSupport
    ((baseBump (E := E)).hasCompactSupport.fderiv (𝕜 := ℝ) |>.comp_left norm_zero)
  refine ⟨max C 0, le_max_right _ _, fun n x v => ?_⟩
  have hi : ‖((n : ℝ) + 1)⁻¹‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
  rw [fderiv_cutoff, norm_mul]
  calc
    _ ≤ 1 * (‖fderiv ℝ (baseBump (E := E)) (((n : ℝ) + 1)⁻¹ • x)‖ * ‖v‖) :=
      mul_le_mul hi (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _) (by norm_num)
    _ ≤ max C 0 * ‖v‖ := by
      rw [one_mul]
      gcongr
      exact (hC (mem_range_self _)).trans (le_max_left _ _)

end Submission.Obl.Entropy__transport_integrated_multiplier
