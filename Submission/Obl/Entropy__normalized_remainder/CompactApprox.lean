import Submission.Obl.Entropy__normalized_remainder.SmoothCutoff

/-! # Smooth approximation of compactly supported C1 functions -/

set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.Entropy__normalized_remainder

open MeasureTheory Filter ContinuousLinearMap
open scoped Convolution Topology

noncomputable def shrinkingBump (m n : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)) :=
  ⟨((n : ℝ) + 1)⁻¹ / 2, ((n : ℝ) + 1)⁻¹,
    by positivity, half_lt_self (by positivity)⟩

lemma shrinkingBump_tendsto (m : ℕ) :
    Tendsto (fun n => (shrinkingBump m n).rOut) atTop (𝓝 0) := cutoff_scale_tendsto

variable {m : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

noncomputable def compactApprox (n : ℕ) (f : EuclideanSpace ℝ (Fin m) → V) :
    EuclideanSpace ℝ (Fin m) → V :=
  (shrinkingBump m n).normed volume ⋆[lsmul ℝ ℝ, volume] f

omit [CompleteSpace V] in
lemma compactApprox_contDiff (n : ℕ) {f : EuclideanSpace ℝ (Fin m) → V}
    (hf : Continuous f) : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (compactApprox n f) :=
  (shrinkingBump m n).hasCompactSupport_normed.contDiff_convolution_left _
    (shrinkingBump m n).contDiff_normed hf.locallyIntegrable

omit [CompleteSpace V] in
lemma compactApprox_hasCompactSupport (n : ℕ) {f : EuclideanSpace ℝ (Fin m) → V}
    (hf : HasCompactSupport f) : HasCompactSupport (compactApprox n f) :=
  (shrinkingBump m n).hasCompactSupport_normed.convolution _ hf

lemma compactApprox_tendsto {f : EuclideanSpace ℝ (Fin m) → V}
    (hf : Continuous f) (x : EuclideanSpace ℝ (Fin m)) :
    Tendsto (fun n => compactApprox n f x) atTop (𝓝 (f x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous (shrinkingBump_tendsto m) hf x

omit [CompleteSpace V] in
lemma compactApprox_norm_le (n : ℕ) (f : EuclideanSpace ℝ (Fin m) → V)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (x : EuclideanSpace ℝ (Fin m)) :
    ‖compactApprox n f x‖ ≤ C := by
  let φ := shrinkingBump m n
  change ‖∫ y, φ.normed volume y • f (x - y)‖ ≤ C
  calc
    _ ≤ ∫ y, φ.normed volume y * C := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const C)
      exact Eventually.of_forall fun y => by
        rw [norm_smul, Real.norm_of_nonneg (φ.nonneg_normed y)]
        exact mul_le_mul_of_nonneg_left (hC (x - y)) (φ.nonneg_normed y)
    _ = C := by rw [integral_mul_const, φ.integral_normed, one_mul]

omit [CompleteSpace V] in
lemma compactApprox_fderiv (n : ℕ) {f : EuclideanSpace ℝ (Fin m) → V}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (x : EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ (compactApprox n f) x = compactApprox n (fderiv ℝ f) x := by
  have h := hfc.hasFDerivAt_convolution_right (μ := volume) (lsmul ℝ ℝ)
    (shrinkingBump m n).integrable_normed.locallyIntegrable hf x
  unfold compactApprox
  rw [h.fderiv]
  have hL : (lsmul ℝ ℝ (E := V)).precompR (EuclideanSpace ℝ (Fin m)) =
      lsmul ℝ ℝ (E := EuclideanSpace ℝ (Fin m) →L[ℝ] V) := by
    ext a l
    rfl
  rw [hL]

lemma compactApprox_fderiv_tendsto {f : EuclideanSpace ℝ (Fin m) → V}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (x : EuclideanSpace ℝ (Fin m)) :
    Tendsto (fun n => fderiv ℝ (compactApprox n f) x) atTop (𝓝 (fderiv ℝ f x)) := by
  simp_rw [compactApprox_fderiv _ hf hfc]
  exact compactApprox_tendsto (hf.continuous_fderiv one_ne_zero) x

omit [CompleteSpace V] in
lemma compactApprox_bounds {f : EuclideanSpace ℝ (Fin m) → V}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    ∃ C₀ C₁ : ℝ, (∀ n x, ‖compactApprox n f x‖ ≤ C₀) ∧
      (∀ n x, ‖fderiv ℝ (compactApprox n f) x‖ ≤ C₁) := by
  obtain ⟨C₀, h₀⟩ := hfc.exists_bound_of_continuous hf.continuous
  obtain ⟨C₁, h₁⟩ := (hfc.fderiv ℝ).exists_bound_of_continuous
    (hf.continuous_fderiv one_ne_zero)
  refine ⟨C₀, C₁, fun n x => compactApprox_norm_le n f h₀ x, fun n x => ?_⟩
  rw [compactApprox_fderiv _ hf hfc]
  exact compactApprox_norm_le n _ h₁ x

end Submission.Obl.Entropy__normalized_remainder
