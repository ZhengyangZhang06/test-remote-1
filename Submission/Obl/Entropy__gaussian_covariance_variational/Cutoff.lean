import Mathlib

open MeasureTheory Filter
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__gaussian_covariance_variational

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

/-- A fixed smooth cutoff, subsequently dilated to larger balls. -/
noncomputable def cutoffBase : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩

lemma cutoffBase_contDiff : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
    (cutoffBase : E → ℝ) := cutoffBase.contDiff

noncomputable def cutoff (n : ℕ) (x : E) : ℝ :=
  cutoffBase (((n : ℝ) + 1)⁻¹ • x)

lemma cutoff_contDiff (n : ℕ) : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (cutoff (m := m) n) :=
  cutoffBase_contDiff.comp (contDiff_id.const_smul _)

lemma cutoff_compact (n : ℕ) : HasCompactSupport (cutoff (m := m) n) :=
  cutoffBase.hasCompactSupport.comp_smul (inv_ne_zero (by positivity))

lemma cutoff_bounds (n : ℕ) (x : E) : 0 ≤ cutoff n x ∧ cutoff n x ≤ 1 :=
  ⟨cutoffBase.nonneg, cutoffBase.le_one⟩

lemma cutoff_tendsto (x : E) : Tendsto (fun n => cutoff n x) atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    have ha : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp ha
  have h := cutoffBase.continuous.continuousAt.tendsto.comp (ht.smul_const x)
  have hzero : (cutoffBase : E → ℝ) 0 = 1 :=
    cutoffBase.one_of_mem_closedBall (by simp [cutoffBase])
  simpa only [Function.comp_def, cutoff, zero_smul, hzero] using h

lemma cutoff_fderiv (n : ℕ) (x v : E) :
    fderiv ℝ (cutoff n) x v = ((n : ℝ) + 1)⁻¹ *
      fderiv ℝ (cutoffBase : E → ℝ) (((n : ℝ) + 1)⁻¹ • x) v := by
  have h := (cutoffBase_contDiff.differentiable (by simp)
    (((n : ℝ) + 1)⁻¹ • x)).hasFDerivAt
  have h' := h.comp x ((hasFDerivAt_id x).const_smul ((n : ℝ) + 1)⁻¹)
  change fderiv ℝ (fun y : E => cutoffBase (((n : ℝ) + 1)⁻¹ • y)) x v = _
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] using
    congrArg (fun L : E →L[ℝ] ℝ => L v) h'.fderiv

lemma cutoff_derivative_bounds : ∃ C : ℝ, 0 ≤ C ∧
    (∀ n (x v : E), ‖fderiv ℝ (cutoff n) x v‖ ≤ C * ‖v‖) ∧
    ∀ (x v : E), Tendsto (fun n => fderiv ℝ (cutoff n) x v) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := (cutoffBase.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (cutoffBase_contDiff.continuous_fderiv (by simp))
  have hC0 : 0 ≤ C := (norm_nonneg (fderiv ℝ (cutoffBase : E → ℝ) 0)).trans (hC 0)
  have hn (n : ℕ) : 0 ≤ ((n : ℝ) + 1)⁻¹ ∧ ((n : ℝ) + 1)⁻¹ ≤ 1 := by
    constructor
    · positivity
    · exact inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have hbound (n : ℕ) (x v : E) : ‖fderiv ℝ (cutoff n) x v‖ ≤
      ((n : ℝ) + 1)⁻¹ * (C * ‖v‖) := by
    rw [cutoff_fderiv, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hn n).1]
    exact mul_le_mul_of_nonneg_left
      ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)))
      (hn n).1
  refine ⟨C, hC0, fun n x v => (hbound n x v).trans ?_, ?_⟩
  · exact mul_le_of_le_one_left (mul_nonneg hC0 (norm_nonneg _)) (hn n).2
  · intro x v
    apply squeeze_zero_norm (fun n => hbound n x v)
    have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      have ha : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
      exact tendsto_inv_atTop_zero.comp ha
    simpa using ht.mul_const (C * ‖v‖)

end Submission.Obl.Entropy__gaussian_covariance_variational
