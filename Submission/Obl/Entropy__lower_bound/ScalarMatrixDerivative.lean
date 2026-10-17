import Submission.Obl.Entropy__lower_bound.GaussianMatrixInverse

/-!
# Functional calculus at scalar matrices

The derivative in a symmetric direction of `f(A)` at `r I` is multiplication
by `f'(r)`. This is the local calculation used at the Gaussian starting point
of the affine-normalization homotopy in Proposition 2.3 of the supplied paper.
-/

open Set Filter
open scoped Topology Matrix.Norms.L2Operator

namespace Submission.Obl.Entropy__lower_bound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem matrix_spectrum_continuousOn (f : ℝ → ℝ) (A : Matrix ι ι ℝ) :
    ContinuousOn f (spectrum ℝ A) :=
  A.finite_real_spectrum.continuousOn f

/-- Differentiation of real functional calculus at a scalar matrix, within the
symmetric matrices. No differentiability of eigenvectors is needed. -/
theorem hasFDerivWithinAt_cfc_scalar {f : ℝ → ℝ} {r d : ℝ}
    (hf : HasDerivAt f d r) :
    HasFDerivWithinAt (fun A : Matrix ι ι ℝ => cfc f A)
      (d • ContinuousLinearMap.id ℝ (Matrix ι ι ℝ))
      {A | A.IsHermitian} (algebraMap ℝ (Matrix ι ι ℝ) r) := by
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hscalar⟩ := Metric.eventually_nhds_iff.mp
    (Asymptotics.isLittleO_iff.mp hf.isLittleO hε)
  have hball : Metric.ball (algebraMap ℝ (Matrix ι ι ℝ) r) δ ∈
      𝓝[{A : Matrix ι ι ℝ | A.IsHermitian}]
        (algebraMap ℝ (Matrix ι ι ℝ) r) :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hδ)
  filter_upwards [self_mem_nhdsWithin, hball] with A hA hdist
  have hc (g : ℝ → ℝ) : ContinuousOn g (spectrum ℝ A) :=
    matrix_spectrum_continuousOn g A
  have hshift : cfc (fun x : ℝ => x - r) A = A - algebraMap ℝ (Matrix ι ι ℝ) r := by
    rw [cfc_sub (fun x : ℝ => x) (fun _ => r) A (hc _) (hc _)]
    change cfc (id : ℝ → ℝ) A - _ = _
    rw [cfc_id ℝ A hA.isSelfAdjoint, cfc_const r A hA.isSelfAdjoint]
  have herr : cfc (fun x : ℝ => f x - f r - d * (x - r)) A =
      cfc f A - cfc f (algebraMap ℝ (Matrix ι ι ℝ) r) -
        (d • ContinuousLinearMap.id ℝ (Matrix ι ι ℝ))
          (A - algebraMap ℝ (Matrix ι ι ℝ) r) := by
    rw [cfc_sub _ _ A (hc _) (hc _), cfc_sub _ _ A (hc _) (hc _),
      cfc_const (f r) A hA.isSelfAdjoint, cfc_algebraMap]
    change cfc f A - algebraMap ℝ (Matrix ι ι ℝ) (f r) -
      cfc (fun x : ℝ => d • (x - r)) A = _
    rw [cfc_smul d _ A (hc _), hshift]
    rfl
  rw [← herr]
  apply norm_cfc_le (mul_nonneg hε.le (norm_nonneg _))
  intro x hx
  have hxshift : x - r ∈ spectrum ℝ (A - algebraMap ℝ (Matrix ι ι ℝ) r) := by
    rw [← hshift, cfc_map_spectrum _ A hA.isSelfAdjoint (hc _)]
    exact ⟨x, hx, rfl⟩
  have hxnorm : ‖x - r‖ ≤ ‖A - algebraMap ℝ (Matrix ι ι ℝ) r‖ :=
    IsometricContinuousFunctionalCalculus.norm_spectrum_le _ hxshift
      (hA.isSelfAdjoint.sub (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all r)))
  have hnear : dist x r < δ := by
    rw [dist_eq_norm]
    exact hxnorm.trans_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hdist)
  have hbound := hscalar hnear
  simp only [smul_eq_mul] at hbound
  calc
    ‖f x - f r - d * (x - r)‖ = ‖f x - f r - (x - r) * d‖ := by rw [mul_comm d]
    _ ≤ ε * ‖x - r‖ := hbound
    _ ≤ ε * ‖A - algebraMap ℝ (Matrix ι ι ℝ) r‖ :=
      mul_le_mul_of_nonneg_left hxnorm hε.le

/-- Functional calculus as a self-map of the real vector space of symmetric
matrices. -/
noncomputable def selfAdjointCFC (f : ℝ → ℝ)
    (A : selfAdjoint (Matrix ι ι ℝ)) : selfAdjoint (Matrix ι ι ℝ) :=
  ⟨cfc f (A : Matrix ι ι ℝ), cfc_predicate _ _⟩

/-- On the symmetric matrix space, the derivative at `r I` is `f'(r)` times
the identity linear map. -/
theorem hasFDerivAt_selfAdjointCFC_scalar {f : ℝ → ℝ} {r d : ℝ}
    (hf : HasDerivAt f d r) :
    HasFDerivAt (selfAdjointCFC (ι := ι) f)
      (d • ContinuousLinearMap.id ℝ (selfAdjoint (Matrix ι ι ℝ)))
      (r • (1 : selfAdjoint (Matrix ι ι ℝ))) := by
  have ht : Tendsto (fun A : selfAdjoint (Matrix ι ι ℝ) => (A : Matrix ι ι ℝ))
      (𝓝 (r • (1 : selfAdjoint (Matrix ι ι ℝ))))
      (𝓝[{A : Matrix ι ι ℝ | A.IsHermitian}]
        (algebraMap ℝ (Matrix ι ι ℝ) r)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Algebra.algebraMap_eq_smul_one, selfAdjoint.val_smul,
        selfAdjoint.val_one] using
        (continuous_subtype_val.tendsto (r • (1 : selfAdjoint (Matrix ι ι ℝ))))
    · exact Eventually.of_forall fun A => A.property
  have h := (hasFDerivWithinAt_cfc_scalar (ι := ι) hf).isLittleO.comp_tendsto ht
  rw [hasFDerivAt_iff_isLittleO, ← Asymptotics.isLittleO_norm_left,
    ← Asymptotics.isLittleO_norm_right]
  rw [← Asymptotics.isLittleO_norm_left, ← Asymptotics.isLittleO_norm_right] at h
  change (fun A : selfAdjoint (Matrix ι ι ℝ) =>
    ‖cfc f (A : Matrix ι ι ℝ) - cfc f ((r • (1 : selfAdjoint (Matrix ι ι ℝ))) : Matrix ι ι ℝ) -
      d • ((A : Matrix ι ι ℝ) - ((r • (1 : selfAdjoint (Matrix ι ι ℝ))) : Matrix ι ι ℝ))‖) =o[𝓝 (r • 1)]
    (fun A : selfAdjoint (Matrix ι ι ℝ) =>
      ‖(A : Matrix ι ι ℝ) - ((r • (1 : selfAdjoint (Matrix ι ι ℝ))) : Matrix ι ι ℝ)‖)
  simpa only [Function.comp_def, Algebra.algebraMap_eq_smul_one,
    selfAdjoint.val_smul, selfAdjoint.val_one, smul_apply,
    ContinuousLinearMap.id_apply] using h

/-- The hazard derivative at every scalar symmetric matrix. -/
theorem hasFDerivAt_selfAdjoint_gaussianHazard_scalar (r : ℝ) :
    HasFDerivAt (selfAdjointCFC (ι := ι) gaussianHazard)
      ((gaussianHazard r * gaussianGap r) •
        ContinuousLinearMap.id ℝ (selfAdjoint (Matrix ι ι ℝ)))
      (r • (1 : selfAdjoint (Matrix ι ι ℝ))) :=
  hasFDerivAt_selfAdjointCFC_scalar (hasDerivAt_gaussianHazard r)

/-- The derivative of the inverse parametrization at every positive scalar
symmetric matrix. -/
theorem hasFDerivAt_selfAdjoint_inverseGaussianHazard_scalar {r : ℝ} (hr : 0 < r) :
    HasFDerivAt (selfAdjointCFC (ι := ι) inverseGaussianHazard)
      ((r * gaussianGap (inverseGaussianHazard r))⁻¹ •
        ContinuousLinearMap.id ℝ (selfAdjoint (Matrix ι ι ℝ)))
      (r • (1 : selfAdjoint (Matrix ι ι ℝ))) := by
  apply hasFDerivAt_selfAdjointCFC_scalar
  convert! (hasStrictDerivAt_inverseGaussianHazard hr).hasDerivAt using 1
  rw [(hasDerivAt_gaussianHazard _).deriv, gaussianHazard_inverseGaussianHazard hr]
  simp only [gaussianGap, gaussianHazard_inverseGaussianHazard hr]

/-- The derivative used at the zero of the Gaussian normalization map. -/
theorem hasFDerivAt_selfAdjoint_inverseGaussianHazard_at_zero :
    HasFDerivAt (selfAdjointCFC (ι := ι) inverseGaussianHazard)
      ((deriv gaussianHazard 0)⁻¹ •
        ContinuousLinearMap.id ℝ (selfAdjoint (Matrix ι ι ℝ)))
      (gaussianHazard 0 • (1 : selfAdjoint (Matrix ι ι ℝ))) := by
  apply hasFDerivAt_selfAdjointCFC_scalar
  simpa only [inverseGaussianHazard_gaussianHazard] using
    (hasStrictDerivAt_inverseGaussianHazard (gaussianHazard_pos 0)).hasDerivAt

omit [DecidableEq ι] in
/-- The symmetric matrix space is finite dimensional over the reals. -/
theorem finiteDimensional_selfAdjointMatrix :
    FiniteDimensional ℝ (selfAdjoint (Matrix ι ι ℝ)) := by
  let inclusion : selfAdjoint (Matrix ι ι ℝ) →ₗ[ℝ] Matrix ι ι ℝ :=
    { toFun := Subtype.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective inclusion Subtype.val_injective

/-- The Gaussian normalization map has positive derivative determinant at its
zero, as required by the local degree computation in Proposition 2.3. -/
theorem det_fderiv_selfAdjoint_inverseGaussianHazard_pos :
    0 < LinearMap.det
      (fderiv ℝ (selfAdjointCFC (ι := ι) inverseGaussianHazard)
        (gaussianHazard 0 • (1 : selfAdjoint (Matrix ι ι ℝ)))).toLinearMap := by
  rw [(hasFDerivAt_selfAdjoint_inverseGaussianHazard_at_zero (ι := ι)).fderiv]
  change 0 < LinearMap.det ((deriv gaussianHazard 0)⁻¹ •
    (LinearMap.id : selfAdjoint (Matrix ι ι ℝ) →ₗ[ℝ] selfAdjoint (Matrix ι ι ℝ)))
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
  exact pow_pos (inv_pos.mpr (deriv_gaussianHazard_pos 0)) _

/-- Within the positive definite cone, the Gaussian normalization map has the
unique zero `q(0) I`. -/
theorem cfc_inverseGaussianHazard_eq_zero_iff {J : Matrix ι ι ℝ} (hJ : J.PosDef) :
    cfc inverseGaussianHazard J = 0 ↔
      J = algebraMap ℝ (Matrix ι ι ℝ) (gaussianHazard 0) := by
  constructor
  · intro h
    calc
      J = cfc gaussianHazard (cfc inverseGaussianHazard J) :=
        (cfc_gaussianHazard_inverseGaussianHazard hJ).symm
      _ = algebraMap ℝ (Matrix ι ι ℝ) (gaussianHazard 0) := by
        rw [h, cfc_apply_zero]
  · intro h
    rw [h, cfc_algebraMap, inverseGaussianHazard_gaussianHazard, map_zero]

end Submission.Obl.Entropy__lower_bound
