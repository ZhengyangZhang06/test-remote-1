import Submission.Obl.Entropy__smooth_gaussian_transport.HessianCurrying
import Submission.Obl.Entropy__smooth_gaussian_transport.GaussianHeat
import Submission.Obl.Entropy__smooth_gaussian_transport.SmoothLogDet

open Set
open scoped RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def hessianOperator (m : ℕ) :
    (E m [×2]→L[ℝ] ℝ) →L[ℝ] (E m →L[ℝ] E m) :=
  (ContinuousLinearMap.compL ℝ (E m) (E m →L[ℝ] ℝ) (E m)
    (InnerProductSpace.toDual ℝ (E m)).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
      (hessianCurry (E m) ℝ).toContinuousLinearEquiv.toContinuousLinearMap

theorem hessianOperator_inner {m : ℕ} (B : E m [×2]→L[ℝ] ℝ) (v w : E m) :
    inner ℝ (hessianOperator m B v) w = B ![v, w] := by
  change (InnerProductSpace.toDual ℝ (E m))
    ((InnerProductSpace.toDual ℝ (E m)).symm (hessianCurry (E m) ℝ B v)) w = _
  rw [LinearIsometryEquiv.apply_symm_apply, hessianCurry_apply]

theorem hessianOperator_iteratedFDeriv {m : ℕ} {f : E m → ℝ}
    (hf : ContDiff ℝ 2 f) (x : E m) :
    hessianOperator m (iteratedFDeriv ℝ 2 f x) = fderiv ℝ (gradient f) x := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ENat) + 1 ≤ 2)).differentiable_one
  have hh := ((InnerProductSpace.toDual ℝ (E m)).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp
    x (hd x).hasFDerivAt).fderiv
  change (InnerProductSpace.toDual ℝ (E m)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (hessianCurry (E m) ℝ (iteratedFDeriv ℝ 2 f x)) = fderiv ℝ (gradient f) x
  rw [hessianCurry_iteratedFDeriv]
  convert! hh.symm using 1

noncomputable def hessianTrace (m : ℕ) : (E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin m, ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E m) ℝ
    ![(EuclideanSpace.basisFun (Fin m) ℝ) i, (EuclideanSpace.basisFun (Fin m) ℝ) i]

theorem hessianTrace_apply {m : ℕ} (B : E m [×2]→L[ℝ] ℝ) :
    hessianTrace m B = ∑ i : Fin m, B ![(EuclideanSpace.basisFun (Fin m) ℝ) i,
      (EuclideanSpace.basisFun (Fin m) ℝ) i] := by
  simp only [hessianTrace, ContinuousLinearMap.sum_apply, ContinuousMultilinearMap.apply_apply]

theorem laplacian_eq_hessianTrace {m : ℕ} {f : E m → ℝ} (hf : ContDiff ℝ 2 f) (x : E m) :
    laplacian f x = hessianTrace m (iteratedFDeriv ℝ 2 f x) := by
  rw [hessianTrace_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ENat) + 1 ≤ 2)).differentiable_one
  have hh := ((ContinuousLinearMap.apply ℝ ℝ ((EuclideanSpace.basisFun (Fin m) ℝ) i)).hasFDerivAt.comp
    x (hd x).hasFDerivAt).fderiv
  simp only [Function.comp_def, ContinuousLinearMap.apply_apply] at hh
  rw [iteratedFDeriv_two_apply]
  change fderiv ℝ (fun z => fderiv ℝ f z ((EuclideanSpace.basisFun (Fin m) ℝ) i)) x
    ((EuclideanSpace.basisFun (Fin m) ℝ) i) = _
  rw [hh]
  rfl

noncomputable def linearizedTraceCLM {m : ℕ} (A : E m →L[ℝ] E m) :
    (E m →L[ℝ] E m) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := linearizedTrace A
      map_add' := linearizedTrace_add A
      map_smul' := fun c B => linearizedTrace_smul A B c }

noncomputable def principalHessian {m : ℕ} (A : E m →L[ℝ] E m) :
    (E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ := (linearizedTraceCLM A).comp (hessianOperator m)

theorem principalHessian_apply {m : ℕ} (A : E m →L[ℝ] E m) (B : E m [×2]→L[ℝ] ℝ) :
    principalHessian A B = linearizedTrace A (hessianOperator m B) := rfl

end Submission.Obl.Entropy__smooth_gaussian_transport
