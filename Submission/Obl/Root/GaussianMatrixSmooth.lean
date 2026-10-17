import Submission.Lib.GaussianTransport.GaussianMatrixInverse

/-!
# Smooth matrix Gaussian functions

The Gaussian tail is a finite integral of matrix exponentials. Integration is
a bounded linear map on continuous functions on the unit interval, so this
representation yields smoothness without choosing smooth eigenvectors.
-/

open MeasureTheory Matrix Set
open scoped unitInterval Matrix.Norms.L2Operator ContDiff

namespace Submission.Obl.Root.GaussianMatrixSmooth

open Submission.Lib.GaussianTransport

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "Mat" => Matrix ι ι ℝ

private lemma integrable_continuous (f : C(I, Mat)) : Integrable f :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Integration on the unit interval as a bounded linear operator. -/
noncomputable def unitIntegral : C(I, Mat) →L[ℝ] Mat :=
  ({ toFun := fun f => ∫ t : I, f t
     map_add' := fun f g => integral_add (integrable_continuous f) (integrable_continuous g)
     map_smul' := fun c f => integral_smul c f } : C(I, Mat) →ₗ[ℝ] Mat).mkContinuous 1 (by
      intro f
      simpa using norm_integral_le_of_norm_le_const (μ := (volume : Measure I))
        (Filter.Eventually.of_forall (fun t => f.norm_coe_le_norm t)))

@[simp] lemma unitIntegral_apply (f : C(I, Mat)) : unitIntegral f = ∫ t : I, f t := rfl

/-- The path `t ↦ t A` depends linearly and continuously on the matrix. -/
noncomputable def timeScale : Mat →L[ℝ] C(I, Mat) :=
  ({ toFun := fun A => ⟨fun t => (t : ℝ) • A, by fun_prop⟩
     map_add' := by
       intro A B
       apply ContinuousMap.ext
       intro t
       exact smul_add (t : ℝ) A B
     map_smul' := by
       intro c A
       apply ContinuousMap.ext
       intro t
       exact smul_comm (t : ℝ) c A } : Mat →ₗ[ℝ] C(I, Mat)).mkContinuous 1 (by
      intro A
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro t
      change ‖(t : ℝ) • A‖ ≤ 1 * ‖A‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
      exact mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg A))

@[simp] lemma timeScale_apply (A : Mat) (t : I) : timeScale A t = (t : ℝ) • A := rfl

private lemma smooth_exp {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    [CompleteSpace R] : ContDiff ℝ ∞ (NormedSpace.exp : R → R) :=
  (show AnalyticOnNhd ℝ NormedSpace.exp univ from fun x _ => NormedSpace.exp_analytic x).contDiff

/-- The Gaussian density, extended by matrix exponentiation. -/
noncomputable def densityMatrix (A : Mat) : Mat :=
  (Real.sqrt (2 * Real.pi))⁻¹ • NormedSpace.exp ((-1 / 2 : ℝ) • A^2)

lemma contDiff_densityMatrix : ContDiff ℝ ∞ (densityMatrix : Mat → Mat) := by
  exact (smooth_exp.comp ((contDiff_id.pow 2).const_smul (-1 / 2 : ℝ))).const_smul _

/-- The Gaussian density path in the Banach algebra of continuous functions. -/
noncomputable def densityPath (A : Mat) : C(I, Mat) :=
  (Real.sqrt (2 * Real.pi))⁻¹ • NormedSpace.exp ((-1 / 2 : ℝ) • (timeScale A)^2)

lemma contDiff_densityPath : ContDiff ℝ ∞ (densityPath : Mat → C(I, Mat)) := by
  exact (smooth_exp.comp (((timeScale (ι := ι)).contDiff.pow 2).const_smul
    (-1 / 2 : ℝ))).const_smul _

lemma densityPath_apply (A : Mat) (t : I) : densityPath A t = densityMatrix ((t : ℝ) • A) := by
  let ev : C(I, Mat) →ₐ[ℝ] Mat :=
    { toFun := fun f => f t
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  letI : NormedAlgebra ℚ C(I, Mat) := NormedAlgebra.restrictScalars ℚ ℝ C(I, Mat)
  have he := NormedSpace.map_exp ev (continuous_eval_const t)
    ((-1 / 2 : ℝ) • (timeScale A)^2)
  change (NormedSpace.exp ((-1 / 2 : ℝ) • (timeScale A)^2)) t =
    NormedSpace.exp ((-1 / 2 : ℝ) • ((t : ℝ) • A)^2) at he
  exact congrArg (fun M : Mat => (Real.sqrt (2 * Real.pi))⁻¹ • M) he

/-- The matrix Gaussian tail, represented by an integral on a fixed interval. -/
noncomputable def tailMatrix (A : Mat) : Mat :=
  (1 / 2 : ℝ) • 1 - A * unitIntegral (densityPath A)

lemma contDiff_tailMatrix : ContDiff ℝ ∞ (tailMatrix : Mat → Mat) :=
  contDiff_const.sub (contDiff_id.mul ((unitIntegral (ι := ι)).contDiff.comp contDiff_densityPath))

/-- The interval representation is valid for every scalar, including zero. -/
lemma normalTail_eq_unitIntegral (a : ℝ) :
    normalCDF (-a) = 1 / 2 - a * ∫ t : I, normalPDF ((t : ℝ) * a) := by
  have hd (t : ℝ) : HasDerivAt (fun s => normalCDF (s * a))
      (normalPDF (t * a) * a) t := by
    simpa only [Function.comp_def, id_eq, one_mul] using
      (hasDerivAt_normalCDF (t * a)).comp t ((hasDerivAt_id t).mul_const a)
  have hc : Continuous (fun t : ℝ => normalPDF (t * a) * a) := by
    exact (contDiff_normalPDF.continuous.comp (continuous_id.mul_const a)).mul_const a
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t _ => hd t)
    (hc.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_mul_const] at hh
  simp only [one_mul, zero_mul, normalCDF_zero] at hh
  have he : (∫ t : I, normalPDF ((t : ℝ) * a)) =
      ∫ t in (0 : ℝ)..1, normalPDF (t * a) := by
    rw [unitInterval.measurePreserving_coe.integral_comp unitInterval.measurableEmbedding_coe
      (fun t => normalPDF (t * a)), integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  rw [he]
  linarith [normalCDF_add_neg a]

/-- The matrix-exponential expression agrees with spectral Gaussian density. -/
lemma densityMatrix_eq_cfc {A : Mat} (hA : A.IsHermitian) :
    densityMatrix A = cfc normalPDF A := by
  have hf : normalPDF = fun a : ℝ =>
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp ((-1 / 2 : ℝ) * a^2) := by
    funext a
    simp only [normalPDF, ProbabilityTheory.gaussianPDFReal, NNReal.coe_one,
      mul_one, sub_zero]
    congr 2 <;> ring
  rw [hf, cfc_const_mul _ _ A (by fun_prop),
    cfc_comp' Real.exp (fun a : ℝ => (-1 / 2 : ℝ) * a^2) A
      (by fun_prop) (by fun_prop) hA.isSelfAdjoint,
    cfc_const_mul (-1 / 2 : ℝ) (fun a : ℝ => a^2) A (by fun_prop),
    cfc_pow_id A 2 hA.isSelfAdjoint, CFC.real_exp_eq_normedSpace_exp]
  rfl

lemma densityPath_eq_cfc {A : Mat} (hA : A.IsHermitian) (t : I) :
    densityPath A t = cfc (fun a => normalPDF ((t : ℝ) * a)) A := by
  rw [densityPath_apply, densityMatrix_eq_cfc (hA.smul (IsSelfAdjoint.all (t : ℝ))),
    cfc_comp' normalPDF (fun a : ℝ => (t : ℝ) * a) A
      contDiff_normalPDF.continuous.continuousOn (by fun_prop) hA.isSelfAdjoint,
    cfc_const_mul_id (t : ℝ) A hA.isSelfAdjoint]

lemma tailMatrix_eq_cfc {A : Mat} (hA : A.IsHermitian) :
    tailMatrix A = cfc (fun a => normalCDF (-a)) A := by
  have hb (x : ℝ) : ‖normalPDF x‖ ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (normalPDF_pos x)]
    simp only [normalPDF, ProbabilityTheory.gaussianPDFReal, NNReal.coe_one,
      mul_one, sub_zero]
    calc
      _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x]))
          (by positivity)
      _ = _ := mul_one _
  have hi := cfc_integral (μ := (volume : Measure I))
    (fun (t : I) a => normalPDF ((t : ℝ) * a))
    (fun _ => (Real.sqrt (2 * Real.pi))⁻¹) A
    (contDiff_normalPDF.continuous.comp
      (continuous_subtype_val.comp continuous_fst |>.mul continuous_snd)).continuousOn
    (Filter.Eventually.of_forall (fun t a _ => hb ((t : ℝ) * a)))
    (integrable_const _).hasFiniteIntegral hA.isSelfAdjoint
  have he : (fun a => normalCDF (-a)) =
      fun a => 1 / 2 - a * ∫ t : I, normalPDF ((t : ℝ) * a) :=
    funext normalTail_eq_unitIntegral
  rw [he, cfc_sub _ _ A (by fun_prop) (A.finite_real_spectrum.continuousOn _),
    cfc_const (1 / 2 : ℝ) A hA.isSelfAdjoint,
    cfc_mul (fun a : ℝ => a) (fun a => ∫ t : I, normalPDF ((t : ℝ) * a)) A
      (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
    cfc_id' ℝ A hA.isSelfAdjoint, hi, Algebra.algebraMap_eq_smul_one]
  unfold tailMatrix
  congr 2
  exact integral_congr_ae (Filter.Eventually.of_forall (densityPath_eq_cfc hA))

/-- A smooth extension of the matrix Gaussian hazard near every symmetric matrix. -/
noncomputable def hazardMatrix (A : Mat) : Mat :=
  densityMatrix A * Ring.inverse (tailMatrix A)

lemma isUnit_tailMatrix {A : Mat} (hA : A.IsHermitian) : IsUnit (tailMatrix A) := by
  rw [tailMatrix_eq_cfc hA]
  exact isUnit_cfc (fun a => normalCDF (-a)) A
    (contDiff_normalCDF.continuous.comp continuous_neg).continuousOn hA.isSelfAdjoint
    (fun a _ => (normalCDF_pos (-a)).ne')

lemma contDiffAt_hazardMatrix {A : Mat} (hA : A.IsHermitian) :
    ContDiffAt ℝ ∞ hazardMatrix A := by
  have hi := contDiffAt_ringInverse (n := ∞) ℝ (isUnit_tailMatrix hA).unit
  rw [IsUnit.unit_spec] at hi
  exact contDiff_densityMatrix.contDiffAt.mul (hi.comp A contDiff_tailMatrix.contDiffAt)

lemma hazardMatrix_eq_cfc {A : Mat} (hA : A.IsHermitian) :
    hazardMatrix A = cfc gaussianHazard A := by
  rw [hazardMatrix, densityMatrix_eq_cfc hA, tailMatrix_eq_cfc hA]
  exact (cfc_map_div normalPDF (fun a => normalCDF (-a)) A
    (fun a _ => (normalCDF_pos (-a)).ne') contDiff_normalPDF.continuous.continuousOn
    (contDiff_normalCDF.continuous.comp continuous_neg).continuousOn hA.isSelfAdjoint).symm

end Submission.Obl.Root.GaussianMatrixSmooth
