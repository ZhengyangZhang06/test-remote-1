import Mathlib

namespace Submission.Obl.Entropy__transport_covariance_completion

open MeasureTheory Filter
open scoped Topology ContDiff

section Cutoff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Dilates of one fixed smooth bump, used to exhaust the ambient space. -/
noncomputable def weakCutoff (n : ℕ) (x : E) : ℝ :=
  (default : ContDiffBump (0 : E)) ((1 / ((n : ℝ) + 1)) • x)

theorem weakCutoff_contDiff (n : ℕ) {s : ENat} : ContDiff ℝ s (weakCutoff (E := E) n) :=
  (default : ContDiffBump (0 : E)).contDiff.comp (contDiff_id.const_smul _)

theorem weakCutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (weakCutoff (E := E) n) :=
  weakCutoff_contDiff n

theorem weakCutoff_compact (n : ℕ) : HasCompactSupport (weakCutoff (E := E) n) :=
  (default : ContDiffBump (0 : E)).hasCompactSupport.comp_smul (by positivity)

theorem weakCutoff_norm_le (n : ℕ) (x : E) : ‖weakCutoff n x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact (default : ContDiffBump (0 : E)).le_one
  · exact (default : ContDiffBump (0 : E)).nonneg

theorem weakCutoff_tendsto (x : E) : Tendsto (fun n => weakCutoff n x) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) • x) atTop (𝓝 (0 : E)) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const x
  have h0 : (default : ContDiffBump (0 : E)) (0 : E) = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    simpa only [Metric.mem_closedBall, dist_self] using
      (default : ContDiffBump (0 : E)).rIn_pos.le
  simpa only [weakCutoff, h0, Function.comp_def] using
    (default : ContDiffBump (0 : E)).continuous.continuousAt.tendsto.comp h

theorem weakCutoff_fderiv (n : ℕ) (x v : E) :
    fderiv ℝ (weakCutoff (E := E) n) x v =
      (1 / ((n : ℝ) + 1)) * fderiv ℝ (default : ContDiffBump (0 : E))
        ((1 / ((n : ℝ) + 1)) • x) v := by
  change fderiv ℝ ((default : ContDiffBump (0 : E)) ∘
    fun y => (1 / ((n : ℝ) + 1)) • y) x v = _
  rw [fderiv_comp (f := fun y : E => (1 / ((n : ℝ) + 1)) • y) x
    ((default : ContDiffBump (0 : E)).contDiff.differentiable (n := ∞) (by simp) _)
    (show DifferentiableAt ℝ (fun y : E => (1 / ((n : ℝ) + 1)) • y) x from
      differentiableAt_id.const_smul _), fderiv_fun_const_smul
        (show DifferentiableAt ℝ (fun y : E => y) x from differentiableAt_id)]
  simp

theorem weakCutoff_fderiv_tendsto (x v : E) :
    Tendsto (fun n => fderiv ℝ (weakCutoff (E := E) n) x v) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) • x) atTop (𝓝 (0 : E)) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const x
  have hd : Continuous (fun y => fderiv ℝ (default : ContDiffBump (0 : E)) y v) :=
    ((default : ContDiffBump (0 : E)).contDiff.continuous_fderiv (n := ∞) (by simp)).clm_apply continuous_const
  simpa only [weakCutoff_fderiv, zero_mul, Function.comp_def] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul (hd.continuousAt.tendsto.comp h)

theorem weakCutoff_fderiv_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ n (x v : E),
    ‖fderiv ℝ (weakCutoff (E := E) n) x v‖ ≤ C * ‖v‖ := by
  let b : ContDiffBump (0 : E) := default
  obtain ⟨C, hC⟩ := (b.hasCompactSupport.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (b.contDiff.continuous_fderiv (n := ∞) (by simp))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C, hC0, fun n x v => ?_⟩
  rw [weakCutoff_fderiv, norm_mul]
  have hn : ‖(1 / ((n : ℝ) + 1))‖ ≤ 1 := by
    have hnpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    rw [Real.norm_eq_abs, abs_of_pos hnpos]
    exact (div_le_one (by positivity)).2 (by linarith [Nat.cast_nonneg (α := ℝ) n])
  calc
    _ ≤ 1 * (C * ‖v‖) := mul_le_mul hn
      ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)))
      (norm_nonneg _) (by positivity)
    _ = C * ‖v‖ := one_mul _

end Cutoff

section Testing
variable {E r : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype r]
  {μ : Measure E}

/-- A weak identity tested against compactly supported smooth functions extends to smooth
`H¹` tests. This cutoff argument needs no special property of the measure. -/
theorem weak_h1_testing_of_contDiff (s : ENat) (hs : (s : WithTop ENat) ≠ 0)
    (e : r → E) {H z : E → ℝ} {v : r → E → ℝ}
    (hH : MemLp H 2 μ) (hv : ∀ i, MemLp (v i) 2 μ)
    (hweak : ∀ w : E → ℝ, ContDiff ℝ s w → HasCompactSupport w →
      (∫ x, H x * w x ∂μ) = ∑ i, ∫ x, v i x * fderiv ℝ w x (e i) ∂μ)
    (hzs : ContDiff ℝ s z) (hz : MemLp z 2 μ)
    (hdz : ∀ i, MemLp (fun x => fderiv ℝ z x (e i)) 2 μ) :
    (∫ x, H x * z x ∂μ) = ∑ i, ∫ x, v i x * fderiv ℝ z x (e i) ∂μ := by
  obtain ⟨C, hC0, hC⟩ := weakCutoff_fderiv_bound (E := E)
  let w (n : ℕ) (x : E) := weakCutoff n x * z x
  have hws n : ContDiff ℝ s (w n) := (weakCutoff_contDiff n).mul hzs
  have hwc n : HasCompactSupport (w n) := (weakCutoff_compact n).mul_right
  have hwder n x (i : r) : fderiv ℝ (w n) x (e i) =
      weakCutoff n x * fderiv ℝ z x (e i) + z x * fderiv ℝ (weakCutoff n) x (e i) := by
    rw [show w n = fun x => weakCutoff n x * z x from rfl,
      fderiv_fun_mul ((weakCutoff_smooth n).differentiable (by simp) x)
        (hzs.differentiable hs x)]
    simp
  have hleft : Tendsto (fun n => ∫ x, H x * w n x ∂μ) atTop
      (𝓝 (∫ x, H x * z x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖H x * z x‖)
    · intro n
      exact hH.aestronglyMeasurable.mul (hws n).continuous.aestronglyMeasurable
    · exact (hH.integrable_mul hz).norm
    · intro n
      filter_upwards [] with x
      change ‖H x * (weakCutoff n x * z x)‖ ≤ _
      calc
        _ = ‖H x * z x‖ * ‖weakCutoff n x‖ := by simp only [norm_mul]; ring
        _ ≤ ‖H x * z x‖ * 1 := mul_le_mul_of_nonneg_left (weakCutoff_norm_le n x) (norm_nonneg _)
        _ = _ := mul_one _
    · filter_upwards [] with x
      simpa only [w, one_mul] using
        (tendsto_const_nhds (x := H x)).mul ((weakCutoff_tendsto x).mul (tendsto_const_nhds (x := z x)))
  have hright (i : r) : Tendsto (fun n => ∫ x, v i x * fderiv ℝ (w n) x (e i) ∂μ)
      atTop (𝓝 (∫ x, v i x * fderiv ℝ z x (e i) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => ‖v i x * fderiv ℝ z x (e i)‖ + C * ‖e i‖ * ‖v i x * z x‖)
    · intro n
      exact (hv i).aestronglyMeasurable.mul
        (((hws n).continuous_fderiv hs).clm_apply continuous_const).aestronglyMeasurable
    · exact ((hv i).integrable_mul (hdz i)).norm.add
        (((hv i).integrable_mul hz).norm.const_mul (C * ‖e i‖))
    · intro n
      filter_upwards [] with x
      rw [hwder, mul_add]
      calc
        _ ≤ ‖v i x * (weakCutoff n x * fderiv ℝ z x (e i))‖ +
            ‖v i x * (z x * fderiv ℝ (weakCutoff n) x (e i))‖ := norm_add_le _ _
        _ = ‖v i x * fderiv ℝ z x (e i)‖ * ‖weakCutoff n x‖ +
            ‖v i x * z x‖ * ‖fderiv ℝ (weakCutoff n) x (e i)‖ := by
          simp only [norm_mul]
          ring
        _ ≤ ‖v i x * fderiv ℝ z x (e i)‖ * 1 +
            ‖v i x * z x‖ * (C * ‖e i‖) := add_le_add
          (mul_le_mul_of_nonneg_left (weakCutoff_norm_le n x) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (hC n x (e i)) (norm_nonneg _))
        _ = _ := by ring
    · filter_upwards [] with x
      have hlim := ((weakCutoff_tendsto x).mul
          (tendsto_const_nhds (x := fderiv ℝ z x (e i)))).add
        ((tendsto_const_nhds (x := z x)).mul (weakCutoff_fderiv_tendsto x (e i)))
      simpa only [hwder, one_mul, mul_zero, add_zero] using
        (tendsto_const_nhds (x := v i x)).mul hlim
  have heq : (fun n => ∫ x, H x * w n x ∂μ) =
      (fun n => ∑ i, ∫ x, v i x * fderiv ℝ (w n) x (e i) ∂μ) :=
    funext (fun n => hweak (w n) (hws n) (hwc n))
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft (tendsto_finsetSum _ (fun i _ => hright i))

/-- The smooth specialization of the cutoff extension. -/
theorem weak_h1_testing (e : r → E) {H z : E → ℝ} {v : r → E → ℝ}
    (hH : MemLp H 2 μ) (hv : ∀ i, MemLp (v i) 2 μ)
    (hweak : ∀ w : E → ℝ, ContDiff ℝ ∞ w → HasCompactSupport w →
      (∫ x, H x * w x ∂μ) = ∑ i, ∫ x, v i x * fderiv ℝ w x (e i) ∂μ)
    (hzs : ContDiff ℝ ∞ z) (hz : MemLp z 2 μ)
    (hdz : ∀ i, MemLp (fun x => fderiv ℝ z x (e i)) 2 μ) :
    (∫ x, H x * z x ∂μ) = ∑ i, ∫ x, v i x * fderiv ℝ z x (e i) ∂μ :=
  weak_h1_testing_of_contDiff ⊤ (by simp) e hH hv hweak hzs hz hdz

end Testing

end Submission.Obl.Entropy__transport_covariance_completion
