import Submission.Obl.Entropy__smooth_gaussian_transport.HessianStructure
import Submission.Lib.EntropyRemainder.MatrixBounds

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def operatorMatrix {m : ℕ} (A : E m →L[ℝ] E m) : Matrix (Fin m) (Fin m) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin m) ℝ).toBasis A.toLinearMap

theorem operatorMatrix_det {m : ℕ} (A : E m →L[ℝ] E m) :
    (operatorMatrix A).det = A.det :=
  LinearMap.det_toMatrix _ _

theorem operatorMatrix_posSemidef {m : ℕ} {A : E m →L[ℝ] E m}
    (hs : A.toLinearMap.IsSymmetric) (hp : ∀ v, 0 ≤ inner ℝ (A v) v) :
    (operatorMatrix A).PosSemidef :=
  (LinearMap.posSemidef_toMatrix_iff (EuclideanSpace.basisFun (Fin m) ℝ)).mpr ⟨hs, hp⟩

theorem operatorMatrix_posDef {m : ℕ} {A : E m →L[ℝ] E m}
    (hs : A.toLinearMap.IsSymmetric) (hp : ∀ v, 0 ≤ inner ℝ (A v) v) (hd : A.det ≠ 0) :
    (operatorMatrix A).PosDef := by
  apply (operatorMatrix_posSemidef hs hp).posDef_iff_det_ne_zero.mpr
  rwa [operatorMatrix_det]

/-- The log determinant is concave on positive definite matrices. -/
theorem log_det_midpoint_concave {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosDef) (hB : B.PosDef) :
    (Real.log A.det + Real.log B.det) / 2 ≤ Real.log (((1 / 2 : ℝ) • (A + B)).det) := by
  let C := (1 / 2 : ℝ) • (A + B)
  have hC : C.PosDef := (hA.add hB).smul (by norm_num)
  have h₁ := Submission.Lib.EntropyRemainder.log_det_supporting_plane hA hC.inv
  have h₂ := Submission.Lib.EntropyRemainder.log_det_supporting_plane hB hC.inv
  have htrace : Matrix.trace (C⁻¹ * A) + Matrix.trace (C⁻¹ * B) = 2 * (m : ℝ) := by
    have hsum : A + B = (2 : ℝ) • C := by dsimp [C]; module
    rw [← Matrix.trace_add, ← Matrix.mul_add, hsum, Matrix.mul_smul,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hC.det_pos.ne'),
      Matrix.trace_smul, Matrix.trace_one]
    simp
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Real.log_inv] at h₁ h₂
  change (Real.log A.det + Real.log B.det) / 2 ≤ Real.log C.det
  linarith

theorem log_det_operator_midpoint_concave {m : ℕ} {A B : E m →L[ℝ] E m}
    (hA : (operatorMatrix A).PosDef) (hB : (operatorMatrix B).PosDef) :
    (Real.log A.det + Real.log B.det) / 2 ≤ Real.log (((1 / 2 : ℝ) • (A + B)).det) := by
  have he : operatorMatrix ((1 / 2 : ℝ) • (A + B)) =
      (1 / 2 : ℝ) • (operatorMatrix A + operatorMatrix B) := by
    simp only [operatorMatrix, ContinuousLinearMap.toLinearMap_smul,
      ContinuousLinearMap.toLinearMap_add, map_smul, map_add]
  have h := log_det_midpoint_concave hA hB
  rw [← he, operatorMatrix_det, operatorMatrix_det, operatorMatrix_det] at h
  exact h

theorem brenier_ae_positive_hessian {m : ℕ} (hm : 1 ≤ m) {V φ : E m → ℝ}
    (hV : Continuous V) (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    ∀ᵐ x ∂volume, DifferentiableAt ℝ (gradient φ) x ∧
      (operatorMatrix (fderiv ℝ (gradient φ) x)).PosDef ∧
      (fderiv ℝ (gradient φ) x).det =
        Submission.Lib.EntropyRemainder.gaussianDensity x * Real.exp (V (gradient φ x)) := by
  filter_upwards [brenier_ae_hessian_structure hm hV hφ hlaw,
    brenier_ae_classical_density hm hV hφ hlaw] with x hx heq
  have hp := operatorMatrix_posDef hx.2.1 hx.2.2.1 hx.2.2.2
  refine ⟨hx.1, hp, ?_⟩
  have hd : 0 < (fderiv ℝ (gradient φ) x).det := by
    simpa only [operatorMatrix_det] using hp.det_pos
  simpa only [abs_of_pos hd] using heq.2

end Submission.Obl.Entropy__smooth_gaussian_transport
