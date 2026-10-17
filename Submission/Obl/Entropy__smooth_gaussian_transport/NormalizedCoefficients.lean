import Submission.Obl.Entropy__smooth_gaussian_transport.HessianCoordinates
import Submission.Obl.Entropy__smooth_gaussian_transport.PrincipalCoefficient
import Submission.Obl.Entropy__smooth_gaussian_transport.MeanLinearization
import Submission.Obl.Entropy__smooth_gaussian_transport.SegmentMean

open MeasureTheory Set
open scoped RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def untransformHessian {m : ℕ} (L : E m ≃L[ℝ] E m) :
    (E m [×2]→L[ℝ] ℝ) →L[ℝ] (E m [×2]→L[ℝ] ℝ) :=
  ContinuousMultilinearMap.compContinuousLinearMapL (F := ℝ)
    (fun _ : Fin 2 => L.symm.toContinuousLinearMap)

noncomputable def normalizedPrincipal {m : ℕ} (L : E m ≃L[ℝ] E m)
    (B : E m [×2]→L[ℝ] ℝ) : (E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  (principalHessian (hessianOperator m (untransformHessian L B))).comp (untransformHessian L)

theorem untransformHessian_comp {m : ℕ} (L : E m ≃L[ℝ] E m) (B : E m [×2]→L[ℝ] ℝ) :
    untransformHessian L (B.compContinuousLinearMap (fun _ => L.toContinuousLinearMap)) = B := by
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [untransformHessian, ContinuousMultilinearMap.compContinuousLinearMapL_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearEquiv.coe_coe,
    L.apply_symm_apply]

theorem untransformHessian_iteratedFDeriv {m : ℕ} {f : E m → ℝ}
    (hf : ContDiff ℝ 2 f) (L : E m ≃L[ℝ] E m) (x : E m) :
    untransformHessian L (iteratedFDeriv ℝ 2 (fun z => f (L z)) x) =
      iteratedFDeriv ℝ 2 f (L x) := by
  rw [show (fun z => f (L z)) = f ∘ L.toContinuousLinearMap from rfl,
    L.toContinuousLinearMap.iteratedFDeriv_comp_right hf x le_rfl, untransformHessian_comp]
  rfl

theorem normalizedPrincipal_contDiffAt {m : ℕ} (L : E m ≃L[ℝ] E m)
    {B : E m [×2]→L[ℝ] ℝ} {n : WithTop ENat}
    (hB : (hessianOperator m (untransformHessian L B)).det ≠ 0) :
    ContDiffAt ℝ n (normalizedPrincipal L) B := by
  let J := (hessianOperator m).comp (untransformHessian L)
  have hP : ContDiffAt ℝ n (fun C => principalHessian (J C)) B :=
    ContDiffAt.comp B (f := J) (principalHessian_contDiffAt hB) J.contDiff.contDiffAt
  exact hP.clm_comp contDiffAt_const

theorem normalizedPrincipal_at_base {m : ℕ} {f : E m → ℝ} (hf : ContDiff ℝ 2 f)
    (x : E m) (L : E m ≃L[ℝ] E m)
    (hL : ∀ B : E m [×2]→L[ℝ] ℝ,
      principalHessian (fderiv ℝ (gradient f) (L x)) (untransformHessian L B) = hessianTrace m B) :
    normalizedPrincipal L (iteratedFDeriv ℝ 2 (fun z => f (L z)) x) = hessianTrace m := by
  apply ContinuousLinearMap.ext
  intro B
  change principalHessian (hessianOperator m (untransformHessian L
    (iteratedFDeriv ℝ 2 (fun z => f (L z)) x))) (untransformHessian L B) = _
  rw [untransformHessian_iteratedFDeriv hf, hessianOperator_iteratedFDeriv hf]
  exact hL B

theorem normalizedPrincipal_increment {m : ℕ} (L : E m ≃L[ℝ] E m)
    {B C : E m [×2]→L[ℝ] ℝ}
    (hB : (operatorMatrix (hessianOperator m (untransformHessian L B))).PosDef)
    (hC : (operatorMatrix (hessianOperator m (untransformHessian L C))).PosDef) :
    segmentMean (normalizedPrincipal L) B C (C - B) =
      Real.log (hessianOperator m (untransformHessian L C)).det -
        Real.log (hessianOperator m (untransformHessian L B)).det := by
  let J := (hessianOperator m).comp (untransformHessian L)
  have he (t : ℝ) : J ((1 - t) • B + t • C) = J B + t • (J C - J B) := by
    simp only [map_add, map_smul, map_sub]
    module
  have hc : ContinuousOn (fun t : ℝ => normalizedPrincipal L ((1 - t) • B + t • C)) (Icc 0 1) := by
    intro t ht
    have hp : (operatorMatrix (J ((1 - t) • B + t • C))).PosDef := by
      rw [he]
      exact positive_hessian_segment hB hC ht
    have hd : (J ((1 - t) • B + t • C)).det ≠ 0 := by
      simpa only [operatorMatrix_det] using hp.det_pos.ne'
    exact ((normalizedPrincipal_contDiffAt L (n := 0) hd).continuousAt.comp (f := fun s : ℝ => (1 - s) • B + s • C)
      (by fun_prop : ContinuousAt (fun s : ℝ => (1 - s) • B + s • C) t)).continuousWithinAt
  change (∫ t in (0 : ℝ)..1, normalizedPrincipal L ((1 - t) • B + t • C)) (C - B) = _
  rw [ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable_of_Icc (by norm_num)),
    log_det_sub_eq_integral hB hC]
  apply intervalIntegral.integral_congr
  intro t ht
  change linearizedTrace (J ((1 - t) • B + t • C)) (J (C - B)) = _
  rw [he, map_sub]
  rfl

end Submission.Obl.Entropy__smooth_gaussian_transport
