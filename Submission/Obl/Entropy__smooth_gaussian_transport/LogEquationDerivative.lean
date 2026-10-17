import Submission.Obl.Entropy__smooth_gaussian_transport.DifferentiateEquation
import Submission.Obl.Entropy__smooth_gaussian_transport.LogDetDerivative

open Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem fderiv_log_det_symmetric {m : ℕ} {A B : E m →L[ℝ] E m}
    (hA : (operatorMatrix A).PosDef) (hB : B.toLinearMap.IsSymmetric) :
    fderiv ℝ (fun T : E m →L[ℝ] E m => Real.log T.det) A B = linearizedTrace A B := by
  have hn : A.det ≠ 0 := by simpa only [operatorMatrix_det] using hA.det_pos.ne'
  have hd := (log_det_contDiffAt (n := 1) hn).differentiableAt_one.hasFDerivAt
  have hz : A + (0 : ℝ) • B = A := by ext v; simp
  have hline := (((hasDerivAt_id (0 : ℝ)).smul_const B).const_add A)
  have hd' : HasFDerivAt (fun T : E m →L[ℝ] E m => Real.log T.det)
      (fderiv ℝ (fun T : E m →L[ℝ] E m => Real.log T.det) A) (A + (0 : ℝ) • B) := by
    simpa only [hz] using hd
  have hh := hd'.comp_hasDerivAt 0 hline
  simpa only [one_smul] using hh.unique (hasDerivAt_log_det_line_zero hA hB)

theorem differentiate_log_det_equation {m : ℕ} {φ q : E m → ℝ}
    (hφ : ContDiff ℝ 3 φ)
    (hpos : ∀ x, (operatorMatrix (fderiv ℝ (gradient φ) x)).PosDef)
    (heq : ∀ x, Real.log (fderiv ℝ (gradient φ) x).det = q x) (v x : E m) :
    principalHessian (fderiv ℝ (gradient φ) x)
      (iteratedFDeriv ℝ 2 (fun y => fderiv ℝ φ y v) x) = fderiv ℝ q x v := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  let H : E m → (E m →L[ℝ] E m) := fun y => hessianOperator m (iteratedFDeriv ℝ 2 φ y)
  have hH : ContDiff ℝ 1 H := (hessianOperator m).contDiff.comp
    (hφ.iteratedFDeriv_right (by norm_num))
  have hHe : H = fderiv ℝ (gradient φ) := funext (hessianOperator_iteratedFDeriv hφ2)
  have hu : ContDiff ℝ 2 (fun y => fderiv ℝ φ y v) :=
    (ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp (hφ.fderiv_right (by norm_num))
  have hDu := symmetric_gradient_derivative (hu.differentiable (by norm_num))
    ((contDiff_one_gradient_of_contDiff_two hu).differentiable_one x).hasFDerivAt
  have hs : (hessianOperator m (iteratedFDeriv ℝ 2 (fun y => fderiv ℝ φ y v) x)).toLinearMap.IsSymmetric := by
    rw [hessianOperator_iteratedFDeriv hu]
    exact hDu
  have hder : fderiv ℝ H x v = hessianOperator m
      (iteratedFDeriv ℝ 2 (fun y => fderiv ℝ φ y v) x) := by
    have hd := ((hessianOperator m).hasFDerivAt.comp x
      (hφ.contDiffAt.differentiableAt_iteratedFDeriv (by norm_num)).hasFDerivAt).fderiv
    rw [hessian_directional_derivative hφ]
    exact congrArg (fun T : E m →L[ℝ] (E m →L[ℝ] E m) => T v) hd
  have hn : (H x).det ≠ 0 := by
    rw [hHe]
    simpa only [operatorMatrix_det] using (hpos x).det_pos.ne'
  have hh := ((log_det_contDiffAt (n := 1) hn).differentiableAt_one.hasFDerivAt.comp x
    (hH.differentiable_one x).hasFDerivAt).fderiv
  have he : (fun y => Real.log (H y).det) = q := by
    funext y
    rw [hHe]
    exact heq y
  change fderiv ℝ (fun y => Real.log (H y).det) x = _ at hh
  rw [he] at hh
  have hv := congrArg (fun T : E m →L[ℝ] ℝ => T v) hh
  change fderiv ℝ q x v = fderiv ℝ (fun T : E m →L[ℝ] E m => Real.log T.det) (H x) (fderiv ℝ H x v) at hv
  rw [hder, hHe, fderiv_log_det_symmetric (hpos x) hs] at hv
  exact hv.symm

end Submission.Obl.Entropy__smooth_gaussian_transport
