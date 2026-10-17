import Submission.Obl.Entropy__transport_integrated_multiplier.Abstract
import Submission.Obl.Entropy__transport_integrated_multiplier.CompactC1
import Submission.Obl.Entropy__transport_integrated_multiplier.BoundedCFC
import Submission.Obl.Entropy__transport_integrated_multiplier.Hessian

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ContDiff ENNReal Matrix.Norms.L2Operator

namespace Submission.Obl.Entropy__transport_integrated_multiplier

open Submission.Lib.GaussianTransport

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "Mat" => Matrix (Fin m) (Fin m) ℝ

/-- Smoothness of the scalar multiplier follows from positivity of the hazard. -/
lemma contDiff_transportRatio : ContDiff ℝ ∞ transportRatio :=
  contDiff_exponentialTransport.div contDiff_gaussianHazard
    (fun a => ne_of_gt (gaussianHazard_pos a))

/-- Coordinate derivatives of a matrix field. -/
noncomputable def matrixDeriv (F : E → Mat) (r : Fin m) (x : E) : Mat :=
  Matrix.of fun i j => fderiv ℝ (fun y => F y i j) x (PiLp.single 2 r 1)

/-- The multiplier density in the frozen statement. -/
noncomputable def multiplierDensity (J Q : E → Mat) (H K : Fin m → E → Mat) (x : E) : ℝ :=
  (∑ i, ∑ j, (Q x * Q x) i j * Matrix.trace ((J x)⁻¹ * H i x * (J x)⁻¹ * H j x)) +
  ∑ r, ∑ s, (J x)⁻¹ r s * Matrix.trace ((K s x * Q x + Q x * K s x) * H r x)

/-- Specialization of the abstract multiplier estimate, requiring only C1 regularity
of the spectral multiplier. -/
theorem transport_multiplier_of_c1
    (A : E → Mat) (hA : ∀ x, (A x).IsHermitian)
    (hAc : ∀ i j, Continuous (fun x => A x i j))
    (hAb : ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R)
    (hQc : ∀ i j, ContDiff ℝ 1 (fun x => cfc transportRatio (A x) i j))
    (V φ : E → ℝ) (hV : ContDiff ℝ ∞ V)
    (hVb : ∃ cmin cmax : ℝ, 0 < cmin ∧ cmin ≤ cmax ∧ ∀ x v : E,
      cmin * ‖v‖^2 ≤ fderiv ℝ (fderiv ℝ V) x v v ∧
      fderiv ℝ (fderiv ℝ V) x v v ≤ cmax * ‖v‖^2)
    (hφ : ContDiff ℝ ∞ φ) :
    let J : E → Mat := fun x => cfc gaussianHazard (A x)
    let Q : E → Mat := fun x => cfc transportRatio (A x)
    let H := matrixDeriv J
    let K := matrixDeriv Q
    let γ := stdGaussian E
    (∀ i j (z : E → ℝ), ContDiff ℝ ∞ z → HasCompactSupport z →
      (∫ x, z x * (-(if i = j then 1 else 0) +
        (J x * Matrix.of (fun u v => fderiv ℝ (fderiv ℝ V) (gradient φ x)
          (PiLp.single 2 u 1) (PiLp.single 2 v 1)) * J x) i j +
        Matrix.trace ((J x)⁻¹ * H i x * (J x)⁻¹ * H j x)) ∂γ) =
          -∑ r, ∑ s, ∫ x, fderiv ℝ z x (PiLp.single 2 s 1) * (J x)⁻¹ s r * H r x i j ∂γ) →
    (∀ r, EntryLp 2 (H r) γ) → (∀ r, EntryLp 2 (K r) γ) →
    Integrable (multiplierDensity J Q H K) γ ∧
      (∫ x, multiplierDensity J Q H K x ∂γ) ≤ ∫ x, ∑ i, ∑ j, (Q x i j)^2 ∂γ := by
  intro J Q H K γ hweak hH hK
  have hAc' : Continuous A := continuous_matrix hAc
  have hq := contDiff_gaussianHazard.continuous
  have hk : Continuous transportRatio := contDiff_transportRatio.continuous
  have hJ : ∀ x, (J x).IsHermitian := fun x => cfc_predicate _ _
  have hQ : ∀ x, (Q x).IsHermitian := fun x => cfc_predicate _ _
  have hJtop : EntryLp ∞ J γ := entryLp_top_cfc hA hAc' hAb hq
  have hMtop : EntryLp ∞ (fun x => (J x)⁻¹) γ :=
    entryLp_top_inverse_cfc hA hAc' hAb hq (fun a => ne_of_gt (gaussianHazard_pos a))
  have hQtop : EntryLp ∞ Q γ := entryLp_top_cfc hA hAc' hAb hk
  refine ⟨integrable_multiplier hMtop hQtop hH hK, ?_⟩
  let B : E → Mat := fun x => Matrix.of fun u v =>
    fderiv ℝ (fderiv ℝ V) (gradient φ x) (PiLp.single 2 u 1) (PiLp.single 2 v 1)
  let W : E → Mat := fun x => J x * B x * J x
  let T : E → Mat := fun x => Matrix.of fun i j =>
    Matrix.trace ((J x)⁻¹ * H i x * (J x)⁻¹ * H j x)
  obtain ⟨cmin, cmax, hcmin, hcmax, hVbound⟩ := hVb
  have hVp (x v : E) : 0 ≤ fderiv ℝ (fderiv ℝ V) x v v :=
    (mul_nonneg hcmin.le (sq_nonneg _)).trans (hVbound x v).1
  have hg : Continuous (gradient φ) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hφ.continuous_fderiv (by simp))
  have hBtop : EntryLp ∞ B γ := entryLp_top_hessian_comp hV hg (hcmin.le.trans hcmax)
    (fun x v => ⟨hVp x v, (hVbound x v).2⟩)
  have hWtop : EntryLp ∞ W γ := (hJtop.mul (r := ∞) hBtop).mul hJtop
  have hWpos (x : E) : (W x).PosSemidef := by
    have h := (hessian_matrix_posSemidef hV hVp (gradient φ x)).mul_mul_conjTranspose_same (J x)
    simpa only [(hJ x).eq] using h
  have hT : EntryLp 1 T γ := fun i j =>
    ((hMtop.mul (r := 2) (hH i) |>.mul (r := 2) hMtop).mul (r := 1) (hH j)).trace
  have hPbound (i j : Fin m) : ∃ C : ℝ, ∀ x, ‖(Q x * Q x) i j‖ ≤ C := by
    apply bounded_observation_of_hermitian
      (f := fun B : Mat => (cfc transportRatio B * cfc transportRatio B) i j) hA hAb
    exact (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn
      ((continuousOn_cfc_hermitian hk).mul (continuousOn_cfc_hermitian hk)))
  apply abstract_multiplier_bound (fun r => PiLp.single 2 r 1) Q W T (fun x => (J x)⁻¹) H K
    hQ (fun x => (hJ x).inv)
    (fun r x => isHermitian_entry_derivative hJ x (PiLp.single 2 r 1)) hWpos
    hQc hPbound hQtop hMtop hWtop hT hH hK (fun _ _ _ _ => rfl)
  intro i j z hz hzc
  have hf : Integrable (fun x => -(if i = j then 1 else 0) + W x i j + T x i j) γ :=
    ((integrable_const _).add ((hWtop i j).integrable (by simp))).add (hT.integrable i j)
  have hb (a : Fin m × Fin m) :
      Integrable (fun x => (J x)⁻¹ a.2 a.1 * H a.1 x i j) γ :=
    ((hH a.1 i j).mul' (r := 2) (hMtop a.2 a.1)).integrable (by norm_num)
  have he := compact_c1_test_of_smooth (fun a : Fin m × Fin m => PiLp.single 2 a.2 1)
    hf hb (fun z hz hzc => by
      simpa only [W, T, B, Matrix.of_apply, Fintype.sum_prod_type, mul_assoc] using hweak i j z hz hzc) hz hzc
  simpa only [Fintype.sum_prod_type, mul_assoc] using he

end Submission.Obl.Entropy__transport_integrated_multiplier
