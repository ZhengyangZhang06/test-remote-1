/-
Adapted from: here:o006

Original proofs by sessions x0016, x0019 and x0062.
-/

import Mathlib

/-!
# Smooth cutoff sequence with bounded derivatives

A fixed smooth bump, dilated by `n + 1`, tends pointwise to one while its
directional derivatives tend to zero. This is the cutoff used to extend the
compact-test Gaussian divergence identity to smooth H1 functions.
-/

set_option backward.isDefEq.respectTransparency false

namespace Submission.Lib.EntropyRemainder

open MeasureTheory Filter
open scoped Topology

noncomputable def cutoffBump (m : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)) :=
  ⟨1, 2, by norm_num, by norm_num⟩

noncomputable def smoothCutoff {m : ℕ} (n : ℕ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  cutoffBump m (((n : ℝ) + 1)⁻¹ • x)

lemma smoothCutoff_contDiff {m : ℕ} (n : ℕ) {k : ℕ∞} :
    ContDiff ℝ k (smoothCutoff (m := m) n) := by
  unfold smoothCutoff
  apply (cutoffBump m).contDiff.comp
  fun_prop

lemma smoothCutoff_hasCompactSupport {m : ℕ} (n : ℕ) :
    HasCompactSupport (smoothCutoff (m := m) n) :=
  (cutoffBump m).hasCompactSupport.comp_smul (by positivity)

lemma smoothCutoff_nonneg {m : ℕ} (n : ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    0 ≤ smoothCutoff n x := (cutoffBump m).nonneg

lemma smoothCutoff_le_one {m : ℕ} (n : ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    smoothCutoff n x ≤ 1 := (cutoffBump m).le_one

lemma smoothCutoff_norm_le {m : ℕ} (n : ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    ‖smoothCutoff n x‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (smoothCutoff_nonneg n x)]
  exact smoothCutoff_le_one n x

lemma cutoff_scale_tendsto : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
  simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma smoothCutoff_tendsto {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) :
    Tendsto (fun n => smoothCutoff n x) atTop (𝓝 1) := by
  have h0 : cutoffBump m (0 : EuclideanSpace ℝ (Fin m)) = 1 :=
    (cutoffBump m).one_of_mem_closedBall (by simp [cutoffBump])
  convert! (cutoffBump m).continuous.continuousAt.tendsto.comp
    (cutoff_scale_tendsto.smul_const x) using 1
  simp [h0]

lemma fderiv_smoothCutoff {m : ℕ} (n : ℕ) (x v : EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ (smoothCutoff n) x v = ((n : ℝ) + 1)⁻¹ *
      fderiv ℝ (cutoffBump m) (((n : ℝ) + 1)⁻¹ • x) v := by
  have hd := ((cutoffBump m).contDiff (n := 1)).differentiable_one
  have h := (hd (((n : ℝ) + 1)⁻¹ • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul (((n : ℝ) + 1)⁻¹))
  change (fderiv ℝ (fun y => cutoffBump m (((n : ℝ) + 1)⁻¹ • y)) x) v = _
  erw [h.fderiv]
  simp

lemma fderiv_smoothCutoff_tendsto {m : ℕ} (x v : EuclideanSpace ℝ (Fin m)) :
    Tendsto (fun n => fderiv ℝ (smoothCutoff n) x v) atTop (𝓝 0) := by
  have hd : Continuous (fun y => fderiv ℝ (cutoffBump m) y v) :=
    (((cutoffBump m).contDiff (n := 1)).continuous_fderiv one_ne_zero).clm_apply
      continuous_const
  simpa only [fderiv_smoothCutoff, zero_mul] using!
    cutoff_scale_tendsto.mul (hd.continuousAt.tendsto.comp (cutoff_scale_tendsto.smul_const x))

lemma fderiv_smoothCutoff_bound (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ n (x v : EuclideanSpace ℝ (Fin m)), ‖fderiv ℝ (smoothCutoff n) x v‖ ≤ C * ‖v‖ := by
  obtain ⟨C, hC⟩ := ((cutoffBump m).hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (((cutoffBump m).contDiff (n := 1)).continuous_fderiv one_ne_zero)
  have hC0 : 0 ≤ C := (norm_nonneg (fderiv ℝ (cutoffBump m) 0)).trans (hC 0)
  refine ⟨C, hC0, fun n x v => ?_⟩
  have ha0 : 0 ≤ ((n : ℝ) + 1)⁻¹ := by positivity
  have ha1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ (show (1 : ℝ) ≤ (n : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) n])
  rw [fderiv_smoothCutoff, norm_mul, Real.norm_of_nonneg ha0]
  calc
    _ ≤ ‖fderiv ℝ (cutoffBump m) (((n : ℝ) + 1)⁻¹ • x) v‖ :=
      mul_le_of_le_one_left (norm_nonneg _) ha1
    _ ≤ ‖fderiv ℝ (cutoffBump m) (((n : ℝ) + 1)⁻¹ • x)‖ * ‖v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * ‖v‖ := mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)

end Submission.Lib.EntropyRemainder
