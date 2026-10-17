import Submission.Obl.Entropy__smooth_gaussian_transport.HessianOperators
import Submission.Obl.Entropy__smooth_gaussian_transport.TraceNormalization

open scoped RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem hessianTrace_eq_matrix_trace {m : ℕ} (B : E m [×2]→L[ℝ] ℝ) :
    hessianTrace m B = (operatorMatrix (hessianOperator m B)).trace := by
  rw [hessianTrace_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hessianOperator_inner]
  simp only [operatorMatrix, Matrix.diag, LinearMap.toMatrix_apply]
  rw [EuclideanSpace.inner_basisFun_real]
  rfl

theorem hessianOperator_comp {m : ℕ} (B : E m [×2]→L[ℝ] ℝ) (L : E m →L[ℝ] E m) :
    hessianOperator m (B.compContinuousLinearMap (fun _ => L)) =
      L.adjoint.comp ((hessianOperator m B).comp L) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro w
  rw [hessianOperator_inner]
  change B (fun i => L (![v, w] i)) = inner ℝ (L.adjoint (hessianOperator m B (L v))) w
  rw [ContinuousLinearMap.adjoint_inner_left, hessianOperator_inner]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem exists_principal_hessian_normalizer {m : ℕ} {A : E m →L[ℝ] E m}
    (hA : (operatorMatrix A).PosDef) :
    ∃ L : E m ≃L[ℝ] E m, ∀ B : E m [×2]→L[ℝ] ℝ,
      principalHessian A (B.compContinuousLinearMap (fun _ => L.symm.toContinuousLinearMap)) =
        hessianTrace m B := by
  obtain ⟨L, hL⟩ := exists_linearized_trace_normalizer hA
  refine ⟨L, ?_⟩
  intro B
  have he : (B.compContinuousLinearMap (fun _ : Fin 2 => L.symm.toContinuousLinearMap)).compContinuousLinearMap
      (fun _ => L.toContinuousLinearMap) = B := by
    apply ContinuousMultilinearMap.ext
    intro v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearEquiv.coe_coe,
      L.symm_apply_apply]
  rw [principalHessian_apply, hL, ← hessianOperator_comp, ← hessianTrace_eq_matrix_trace, he]

end Submission.Obl.Entropy__smooth_gaussian_transport
