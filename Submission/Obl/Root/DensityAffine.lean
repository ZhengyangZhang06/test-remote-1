import Mathlib
import ChallengeDeps
import Submission.Lib.EntropyTools.DensityMoments

open MeasureTheory
open Submission.Lib.EntropyTools
open scoped Matrix

namespace Submission.Obl.Root.DensityAffine

noncomputable def affineDensity {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun y => |LinearMap.det e.toLinearMap|⁻¹ * f (e.symm (y - b))

/-- Change of variables under an invertible affine map, for a Banach-valued integral. -/
theorem integral_affine {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : E ≃L[ℝ] E)
    (b : E) (g : E → F) :
    (∫ y, g y ∂μ) = ∫ x, |LinearMap.det e.toLinearMap| • g (e x + b) ∂μ := by
  have hs : (fun x => e x + b) '' Set.univ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    exact ⟨e.symm (y - b), Set.mem_univ _, by simp⟩
  have hder (x : E) (_ : x ∈ Set.univ) :
      HasFDerivWithinAt (fun y => e y + b) e.toContinuousLinearMap Set.univ x :=
    (e.hasFDerivAt.add_const b).hasFDerivWithinAt
  have hinj : Set.InjOn (fun x => e x + b) Set.univ := by
    intro x _ y _ h
    exact e.injective (add_right_cancel h)
  simpa only [hs, Measure.restrict_univ, ContinuousLinearMap.det, ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap] using
    integral_image_eq_integral_abs_det_fderiv_smul μ MeasurableSet.univ (f' := fun _ => e.toContinuousLinearMap) hder hinj g

/-- Integrability is preserved by the affine change of variables with its Jacobian. -/
theorem integrable_affine_iff {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : E ≃L[ℝ] E)
    (b : E) (g : E → F) :
    Integrable g μ ↔ Integrable (fun x => |LinearMap.det e.toLinearMap| • g (e x + b)) μ := by
  have hs : (fun x => e x + b) '' Set.univ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    exact ⟨e.symm (y - b), Set.mem_univ _, by simp⟩
  have hder (x : E) (_ : x ∈ Set.univ) :
      HasFDerivWithinAt (fun y => e y + b) e.toContinuousLinearMap Set.univ x :=
    (e.hasFDerivAt.add_const b).hasFDerivWithinAt
  have hinj : Set.InjOn (fun x => e x + b) Set.univ := by
    intro x _ y _ h
    exact e.injective (add_right_cancel h)
  simpa only [hs, IntegrableOn, Measure.restrict_univ, ContinuousLinearMap.det, ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap] using
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ
      MeasurableSet.univ (f' := fun _ => e.toContinuousLinearMap) hder hinj g

/-- The affine image density transports every weighted integral. -/
theorem integral_affineDensity_smul {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → F) :
    (∫ y, affineDensity e b f y • g y) = ∫ x, f x • g (e x + b) := by
  rw [integral_affine volume e b]
  have hd : |LinearMap.det e.toLinearMap| ≠ 0 :=
    abs_ne_zero.mpr e.toLinearEquiv.isUnit_det'.ne_zero
  congr 1
  funext x
  simp [affineDensity, smul_smul, hd]

/-- The affine image density also preserves weighted integrability. -/
theorem integrable_affineDensity_smul_iff {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → F) :
    Integrable (fun y => affineDensity e b f y • g y) ↔
      Integrable (fun x => f x • g (e x + b)) := by
  rw [integrable_affine_iff volume e b]
  have hd : |LinearMap.det e.toLinearMap| ≠ 0 :=
    abs_ne_zero.mpr e.toLinearEquiv.isUnit_det'.ne_zero
  simp [affineDensity, smul_smul, hd]

theorem affineDensity_nonneg {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (y : EuclideanSpace ℝ (Fin n)) :
    0 ≤ affineDensity e b f y :=
  mul_nonneg (inv_nonneg.mpr (abs_nonneg _)) (hf _)

theorem integral_affineDensity {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ y, affineDensity e b f y) = ∫ x, f x := by
  simpa using integral_affineDensity_smul e b f (fun _ => (1 : ℝ))

/-- The mean transforms by the affine map when the density has mass one. -/
theorem mean_affineDensity {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Integrable f) (hfirst : Integrable (fun x => f x • x))
    (hmass : ∫ x, f x = 1) :
    (∫ y, affineDensity e b f y • y) = e (∫ x, f x • x) + b := by
  rw [integral_affineDensity_smul e b]
  have he : Integrable (fun x => f x • e x) := by
    simpa only [map_smul, ContinuousLinearEquiv.coe_coe] using e.toContinuousLinearMap.integrable_comp hfirst
  simp_rw [smul_add]
  rw [integral_add he (hf.smul_const b), integral_smul_const, hmass, one_smul]
  congr 1
  simpa only [map_smul, ContinuousLinearEquiv.coe_coe] using e.integral_comp_comm (fun x => f x • x)

/-- The first moment of the affine image is finite. -/
theorem integrable_first_affineDensity {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Integrable f) (hfirst : Integrable (fun x => f x • x)) :
    Integrable (fun y => affineDensity e b f y • y) := by
  apply (integrable_affineDensity_smul_iff e b f (fun x => x)).mpr
  have he : Integrable (fun x => f x • e x) := by
    simpa only [map_smul, ContinuousLinearEquiv.coe_coe] using e.toContinuousLinearMap.integrable_comp hfirst
  simp_rw [smul_add]
  exact he.add (hf.smul_const b)

/-- The logarithm scaling formula also holds at a zero of the density. -/
theorem mul_log_affineDensity {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    f x * Real.log (affineDensity e b f (e x + b)) =
      f x * Real.log (f x) - f x * Real.log |LinearMap.det e.toLinearMap| := by
  have hd : |LinearMap.det e.toLinearMap| ≠ 0 :=
    abs_ne_zero.mpr e.toLinearEquiv.isUnit_det'.ne_zero
  by_cases hx : f x = 0
  · simp [hx]
  · simp only [affineDensity, add_sub_cancel_right, e.symm_apply_apply,
      Real.log_mul (inv_ne_zero hd) hx, Real.log_inv]
    ring

/-- Finite entropy is preserved by every invertible affine map. -/
theorem integrable_entropy_affineDensity {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Integrable f) (hent : Integrable (fun x => f x * Real.log (f x))) :
    Integrable (fun y => affineDensity e b f y * Real.log (affineDensity e b f y)) := by
  have h := (integrable_affineDensity_smul_iff e b f
    (fun y => Real.log (affineDensity e b f y)))
  simp only [smul_eq_mul] at h
  apply h.mpr
  simp_rw [mul_log_affineDensity]
  exact hent.sub (hf.mul_const _)

/-- Entropy increases by the log absolute determinant under affine transport. -/
theorem entropy_affineDensity {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Integrable f) (hent : Integrable (fun x => f x * Real.log (f x)))
    (hmass : ∫ x, f x = 1) :
    -(∫ y, affineDensity e b f y * Real.log (affineDensity e b f y)) =
      -(∫ x, f x * Real.log (f x)) + Real.log |LinearMap.det e.toLinearMap| := by
  have h := integral_affineDensity_smul e b f
    (fun y => Real.log (affineDensity e b f y))
  simp only [smul_eq_mul] at h
  rw [h]
  simp_rw [mul_log_affineDensity]
  rw [integral_sub hent (hf.mul_const _), integral_mul_const, hmass]
  ring

/-- Matrix of the linear part in the standard Euclidean basis. -/
noncomputable def linMatrix {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis e.toLinearMap

theorem linMatrix_apply {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    e x i = ∑ j, linMatrix e i j * x j := by
  have h := congrFun (LinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis e.toLinearMap x) i
  simpa [linMatrix, Matrix.mulVec, dotProduct,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr] using h.symm

theorem linMatrix_det {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (linMatrix e).det = LinearMap.det e.toLinearMap :=
  LinearMap.det_toMatrix _ _

/-- Centered second moments transform by matrix congruence. -/
theorem covariance_affineDensity {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (b c : EuclideanSpace ℝ (Fin n)) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2)) :
    densityCovariance (affineDensity e b f) (e c + b) =
      linMatrix e * densityCovariance f c * (linMatrix e).transpose := by
  have hc (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
      (e x + b) i - (e c + b) i = ∑ j, linMatrix e i j * (x j - c j) := by
    simpa only [map_sub, PiLp.sub_apply, PiLp.add_apply, add_sub_add_right_eq_sub] using
      linMatrix_apply e (x - c) i
  have hi (i j k l : Fin n) : Integrable (fun x =>
      (linMatrix e i k * linMatrix e j l) * (f x * (x k - c k) * (x l - c l))) :=
    (integrable_density_centered_mul hf0 hf hf2 c k l).const_mul _
  ext i j
  change (∫ y, affineDensity e b f y * (y i - (e c + b) i) * (y j - (e c + b) j)) = _
  have hw := integral_affineDensity_smul e b f
    (fun y => (y i - (e c + b) i) * (y j - (e c + b) j))
  simp only [smul_eq_mul, ← mul_assoc] at hw
  rw [hw]
  simp_rw [hc]
  have hexp (x : EuclideanSpace ℝ (Fin n)) :
      f x * (∑ k, linMatrix e i k * (x k - c k)) *
        (∑ l, linMatrix e j l * (x l - c l)) =
      ∑ k, ∑ l, (linMatrix e i k * linMatrix e j l) *
        (f x * (x k - c k) * (x l - c l)) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hi i j k l))]
  simp_rw [integral_finsetSum _ (fun l _ => hi i j _ l), integral_const_mul]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, densityCovariance, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The determinant of a centered second-moment matrix scales by the determinant squared. -/
theorem covariance_det_affineDensity {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (b c : EuclideanSpace ℝ (Fin n)) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2)) :
    (densityCovariance (affineDensity e b f) (e c + b)).det =
      (LinearMap.det e.toLinearMap) ^ 2 * (densityCovariance f c).det := by
  rw [covariance_affineDensity e b c hf0 hf hf2,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, linMatrix_det]
  ring

/-- The entropy deficit used in the smooth transport argument is affine invariant. -/
theorem entropy_deficit_affineDensity {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f) (hmass : ∫ x, f x = 1)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2))
    (hent : Integrable (fun x => f x * Real.log (f x))) :
    -(∫ y, affineDensity e b f y * Real.log (affineDensity e b f y)) -
        Real.log (densityCovariance (affineDensity e b f)
          (∫ y, affineDensity e b f y • y)).det / 2 =
      -(∫ x, f x * Real.log (f x)) -
        Real.log (densityCovariance f (∫ x, f x • x)).det / 2 := by
  rw [entropy_affineDensity e b hf hent hmass,
    mean_affineDensity e b hf (integrable_density_smul hf0 hf hf2) hmass,
    covariance_det_affineDensity e b _ hf0 hf hf2,
    Real.log_mul (pow_ne_zero _ e.toLinearEquiv.isUnit_det'.ne_zero)
      (ne_of_gt (densityCovariance_det_pos hf0 hf hmass hf2 _)),
    Real.log_pow, Real.log_abs]
  norm_num
  ring

/-- An affine image has the same finite total mass. -/
theorem integrable_affineDensity {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Integrable f) : Integrable (affineDensity e b f) := by
  have h := (integrable_affineDensity_smul_iff e b f (fun _ => (1 : ℝ))).mpr
    (by simpa using hf)
  simpa using h

/-- A finite second moment remains finite after an affine change of coordinates. -/
theorem integrable_second_affineDensity {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2)) :
    Integrable (fun y => affineDensity e b f y * ‖y‖ ^ 2) := by
  have h := integrable_affineDensity_smul_iff e b f (fun y => ‖y‖ ^ 2)
  simp only [smul_eq_mul] at h
  apply h.mpr
  apply integrable_density_mul_of_quadratic_bound hf0 hf hf2
    (by fun_prop) (2 * ‖e.toContinuousLinearMap‖ ^ 2 + 2 * ‖b‖ ^ 2)
  intro x
  rw [abs_of_nonneg (sq_nonneg _)]
  have hlin := e.toContinuousLinearMap.le_opNorm x
  have hsum : ‖e x + b‖ ≤ ‖e.toContinuousLinearMap‖ * ‖x‖ + ‖b‖ :=
    (norm_add_le _ _).trans (by
      simpa only [ContinuousLinearEquiv.coe_coe] using (add_le_add hlin (le_refl ‖b‖)))
  have hsq : ‖e x + b‖ ^ 2 ≤ (‖e.toContinuousLinearMap‖ * ‖x‖ + ‖b‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hsum 2
  nlinarith [sq_nonneg (‖e.toContinuousLinearMap‖ * ‖x‖ - ‖b‖),
    mul_nonneg (sq_nonneg ‖b‖) (sq_nonneg ‖x‖), sq_nonneg ‖e.toContinuousLinearMap‖]


/-- Upper semicontinuity is preserved by the affine image density. -/
theorem upperSemicontinuous_affineDensity {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : UpperSemicontinuous f) : UpperSemicontinuous (affineDensity e b f) := by
  have hpre : UpperSemicontinuous (fun y => f (e.symm (y - b))) :=
    hf.comp (by fun_prop)
  exact (continuous_const.mul continuous_id).comp_upperSemicontinuous hpre
    (fun _ _ h => mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (abs_nonneg _)))

/-- Log concavity on the positive set is preserved by an affine image. -/
theorem log_concave_affineDensity {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x))) :
    ConcaveOn ℝ {y | 0 < affineDensity e b f y}
      (fun y => Real.log (affineDensity e b f y)) := by
  let A : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] EuclideanSpace ℝ (Fin n) :=
    e.symm.toLinearMap.toAffineMap - AffineMap.const ℝ _ (e.symm b)
  have hA (x : EuclideanSpace ℝ (Fin n)) : A x = e.symm (x - b) := by
    simp [A, map_sub]
  have hd : 0 < |LinearMap.det e.toLinearMap|⁻¹ :=
    inv_pos.mpr (abs_pos.mpr e.toLinearEquiv.isUnit_det'.ne_zero)
  have hs : {y | 0 < affineDensity e b f y} = A ⁻¹' {x | 0 < f x} := by
    ext y
    simp only [affineDensity, Set.mem_ofPred_eq, Set.mem_preimage, hA,
      mul_pos_iff_of_pos_left hd]
  rw [hs]
  apply ((hf.comp_affineMap A).add_const (-Real.log |LinearMap.det e.toLinearMap|)).congr
  intro y hy
  have hy' : f (e.symm (y - b)) ≠ 0 := ne_of_gt (by simpa only [Set.mem_preimage,
    Set.mem_ofPred_eq, hA] using hy)
  dsimp only [Pi.add_apply, Function.comp_apply]
  rw [affineDensity, Real.log_mul (ne_of_gt hd) hy', Real.log_inv, hA]
  ring

end Submission.Obl.Root.DensityAffine
