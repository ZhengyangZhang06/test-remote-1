/-
Adapted from: here:o001

Original Section 2 scalar/matrix proof by session x0041.
-/

import Submission.Lib.GaussianTransport.GaussianConvexity

/-!
# The mean-zero spectral bound in affine normalization

In Proposition 2.3 of the supplied paper, convexity gives `E q(A) ≥ q(0) I`
when the symmetric parameter has mean zero. A scalar supporting line, followed
by spectral functional calculus and integration, gives the bound directly.
-/

open MeasureTheory Set

namespace Submission.Lib.GaussianTransport

open scoped MatrixOrder Matrix.Norms.L2Operator

/-- A differentiable convex function lies above each of its tangent lines. -/
theorem convex_tangent_le {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f)
    {s d : ℝ} (hd : HasDerivAt f d s) (a : ℝ) :
    f s + d * (a - s) ≤ f a := by
  rcases lt_trichotomy s a with h | rfl | h
  · have hs := hf.le_slope_of_hasDerivAt (mem_univ _) (mem_univ _) h hd
    rw [slope_def_field] at hs
    have := (le_div_iff₀ (sub_pos.mpr h)).mp hs
    linarith
  · simp
  · have hs := hf.slope_le_of_hasDerivAt (mem_univ _) (mem_univ _) h hd
    rw [slope_def_field] at hs
    have := (div_le_iff₀ (sub_pos.mpr h)).mp hs
    nlinarith

/-- The scalar supporting line for the Gaussian hazard at zero. -/
theorem gaussianHazard_tangent_zero_le (a : ℝ) :
    gaussianHazard 0 + deriv gaussianHazard 0 * a ≤ gaussianHazard a := by
  simpa using convex_tangent_le convexOn_gaussianHazard
    (hasDerivAt_gaussianHazard 0).differentiableAt.hasDerivAt a

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Functional calculus preserves scalar supporting-line inequalities. -/
theorem cfc_affine_lower_bound {f : ℝ → ℝ} (hf : Continuous f)
    {c d : ℝ} (hlower : ∀ a, c + d * a ≤ f a)
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    c • (1 : Matrix ι ι ℝ) + d • A ≤ cfc f A := by
  have h := (cfc_le_iff (fun a => c + d * a) f A
    (by fun_prop) hf.continuousOn hA.isSelfAdjoint).mpr (fun a _ => hlower a)
  rw [cfc_const_add c (fun a => d * a) A (by fun_prop) hA.isSelfAdjoint,
    cfc_const_mul_id d A hA.isSelfAdjoint, Algebra.algebraMap_eq_smul_one] at h
  exact h

/-- The spectral tangent bound used in the normalization argument. -/
theorem cfc_gaussianHazard_tangent_zero_le {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    gaussianHazard 0 • (1 : Matrix ι ι ℝ) + deriv gaussianHazard 0 • A ≤
      cfc gaussianHazard A :=
  cfc_affine_lower_bound contDiff_gaussianHazard.continuous gaussianHazard_tangent_zero_le hA

/-- A scalar lower bound survives squaring a symmetric matrix when nonnegative. -/
theorem scalar_sq_le_matrix_sq {c : ℝ} (hc : 0 ≤ c) {J : Matrix ι ι ℝ}
    (hJ : J.IsHermitian) (hbound : c • (1 : Matrix ι ι ℝ) ≤ J) :
    c ^ 2 • (1 : Matrix ι ι ℝ) ≤ J ^ 2 := by
  have hs : ∀ a ∈ spectrum ℝ J, c ≤ a := by
    apply (algebraMap_le_cfc_iff (fun a : ℝ => a) c J
      continuous_id.continuousOn hJ.isSelfAdjoint).mp
    simpa only [cfc_id' ℝ J hJ.isSelfAdjoint, Algebra.algebraMap_eq_smul_one] using hbound
  have hsq := (algebraMap_le_cfc_iff (fun a : ℝ => a ^ 2) (c ^ 2) J
    (by fun_prop) hJ.isSelfAdjoint).mpr (fun a ha => pow_le_pow_left₀ hc (hs a ha) 2)
  simpa only [cfc_pow_id J 2 hJ.isSelfAdjoint, Algebra.algebraMap_eq_smul_one] using hsq

omit [Fintype ι] in
/-- A positive scalar lower bound implies positive definiteness. -/
theorem posDef_of_pos_scalar_le {c : ℝ} (hc : 0 < c) {J : Matrix ι ι ℝ}
    (hbound : c • (1 : Matrix ι ι ℝ) ≤ J) : J.PosDef := by
  have h := (Matrix.PosDef.one.smul hc).add_posSemidef (Matrix.le_iff.mp hbound)
  convert! h using 1
  abel

/-- The hazard lies below a slope-one line to the right of any fixed parameter. -/
theorem gaussianHazard_le_affine_of_le {l a : ℝ} (ha : l ≤ a) :
    gaussianHazard a ≤ gaussianHazard l - l + a := by
  have h := antitone_gaussianGap ha
  unfold gaussianGap at h
  linarith

/-- A common spectral lower bound gives an affine upper bound for the Jacobian. -/
theorem cfc_gaussianHazard_le_of_spectrum_lower {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) {l : ℝ} (hl : ∀ a ∈ spectrum ℝ A, l ≤ a) :
    cfc gaussianHazard A ≤ (gaussianHazard l - l) • (1 : Matrix ι ι ℝ) + A := by
  have h := (cfc_le_iff gaussianHazard (fun a => gaussianHazard l - l + a) A
    contDiff_gaussianHazard.continuous.continuousOn (by fun_prop) hA.isSelfAdjoint).mpr
      (fun a ha => gaussianHazard_le_affine_of_le (hl a ha))
  rw [cfc_const_add (gaussianHazard l - l) (fun a : ℝ => a) A
    continuous_id.continuousOn hA.isSelfAdjoint,
    cfc_id' ℝ A hA.isSelfAdjoint, Algebra.algebraMap_eq_smul_one] at h
  exact h

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Coordinate evaluation commutes with a matrix integral in the operator norm. -/
theorem matrix_integral_apply {A : α → Matrix ι ι ℝ} (hA : Integrable A μ) (i j : ι) :
    (∫ x, A x ∂μ) i j = ∫ x, A x i j ∂μ := by
  let e : Matrix ι ι ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun M => M i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact (e.toContinuousLinearMap.integral_comp_comm hA).symm

/-- Entrywise normalization is the matrix-valued mean-zero condition. -/
theorem matrix_integral_eq_zero_of_entries {A : α → Matrix ι ι ℝ}
    (hA : Integrable A μ) (hzero : ∀ i j, (∫ x, A x i j ∂μ) = 0) :
    (∫ x, A x ∂μ) = 0 := by
  ext i j
  rw [matrix_integral_apply hA i j, hzero i j]
  rfl

variable [IsProbabilityMeasure μ]

/-- A mean-zero symmetric random matrix satisfies the spectral supporting-line bound. -/
theorem integral_cfc_ge_of_mean_zero {f : ℝ → ℝ} (hf : Continuous f)
    {c d : ℝ} (hlower : ∀ a, c + d * a ≤ f a)
    {A : α → Matrix ι ι ℝ} (hA : ∀ᵐ x ∂μ, (A x).IsHermitian)
    (hAi : Integrable A μ) (hfi : Integrable (fun x => cfc f (A x)) μ)
    (hmean : (∫ x, A x ∂μ) = 0) :
    c • (1 : Matrix ι ι ℝ) ≤ ∫ x, cfc f (A x) ∂μ := by
  have hcint : Integrable (fun _ : α => c • (1 : Matrix ι ι ℝ)) μ := integrable_const _
  have hdint : Integrable (fun x => d • A x) μ := hAi.smul d
  have h := integral_mono_ae
    (hcint.add hdint) hfi (by
      filter_upwards [hA] with x hx
      exact cfc_affine_lower_bound hf hlower hx)
  change (∫ x, c • (1 : Matrix ι ι ℝ) + d • A x ∂μ) ≤ _ at h
  rw [integral_add hcint hdint, integral_smul d A, hmean,
    smul_zero, add_zero] at h
  simpa using h

/-- The normalization condition implies a positive lower bound on the mean Jacobian. -/
theorem integral_gaussianHazard_ge_of_mean_zero
    {A : α → Matrix ι ι ℝ} (hA : ∀ᵐ x ∂μ, (A x).IsHermitian)
    (hAi : Integrable A μ) (hqi : Integrable (fun x => cfc gaussianHazard (A x)) μ)
    (hmean : (∫ x, A x ∂μ) = 0) :
    gaussianHazard 0 • (1 : Matrix ι ι ℝ) ≤ ∫ x, cfc gaussianHazard (A x) ∂μ :=
  integral_cfc_ge_of_mean_zero contDiff_gaussianHazard.continuous
    gaussianHazard_tangent_zero_le hA hAi hqi hmean

/-- The expected Jacobian in normalized coordinates is positive definite. -/
theorem integral_gaussianHazard_posDef_of_mean_zero
    {A : α → Matrix ι ι ℝ} (hA : ∀ᵐ x ∂μ, (A x).IsHermitian)
    (hAi : Integrable A μ) (hqi : Integrable (fun x => cfc gaussianHazard (A x)) μ)
    (hmean : (∫ x, A x ∂μ) = 0) :
    (∫ x, cfc gaussianHazard (A x) ∂μ).PosDef :=
  posDef_of_pos_scalar_le (gaussianHazard_pos 0)
    (integral_gaussianHazard_ge_of_mean_zero hA hAi hqi hmean)

/-- The square of the expected Jacobian has the uniform lower bound from normalization. -/
theorem integral_gaussianHazard_sq_ge_of_mean_zero
    {A : α → Matrix ι ι ℝ} (hA : ∀ᵐ x ∂μ, (A x).IsHermitian)
    (hAi : Integrable A μ) (hqi : Integrable (fun x => cfc gaussianHazard (A x)) μ)
    (hmean : (∫ x, A x ∂μ) = 0) :
    gaussianHazard 0 ^ 2 • (1 : Matrix ι ι ℝ) ≤
      (∫ x, cfc gaussianHazard (A x) ∂μ) ^ 2 :=
  scalar_sq_le_matrix_sq (gaussianHazard_pos 0).le
    (integral_gaussianHazard_posDef_of_mean_zero hA hAi hqi hmean).isHermitian
    (integral_gaussianHazard_ge_of_mean_zero hA hAi hqi hmean)

/-- A uniform spectral lower bound controls the expected Jacobian from above. -/
theorem integral_gaussianHazard_le_of_mean_zero
    {A : α → Matrix ι ι ℝ} (hA : ∀ᵐ x ∂μ, (A x).IsHermitian)
    (hAi : Integrable A μ) (hqi : Integrable (fun x => cfc gaussianHazard (A x)) μ)
    (hmean : (∫ x, A x ∂μ) = 0) {l : ℝ}
    (hl : ∀ᵐ x ∂μ, ∀ a ∈ spectrum ℝ (A x), l ≤ a) :
    (∫ x, cfc gaussianHazard (A x) ∂μ) ≤
      (gaussianHazard l - l) • (1 : Matrix ι ι ℝ) := by
  have hcint : Integrable (fun _ : α =>
      (gaussianHazard l - l) • (1 : Matrix ι ι ℝ)) μ := integrable_const _
  have h := integral_mono_ae hqi (hcint.add hAi) (by
    filter_upwards [hA, hl] with x hx hlx
    exact cfc_gaussianHazard_le_of_spectrum_lower hx hlx)
  change (∫ x, cfc gaussianHazard (A x) ∂μ) ≤
    ∫ x, (gaussianHazard l - l) • (1 : Matrix ι ι ℝ) + A x ∂μ at h
  rw [integral_add hcint hAi, hmean, add_zero] at h
  simpa using h

end Submission.Lib.GaussianTransport
