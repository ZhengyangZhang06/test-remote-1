import Submission.Obl.Entropy__smooth_gaussian_transport.LinearizedEllipticity

open scoped MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem operatorMatrix_comp {m : ℕ} (A B : E m →L[ℝ] E m) :
    operatorMatrix (A.comp B) = operatorMatrix A * operatorMatrix B := by
  exact LinearMap.toMatrix_comp (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin m) ℝ).toBasis (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    A.toLinearMap B.toLinearMap

theorem operatorMatrix_adjoint {m : ℕ} (A : E m →L[ℝ] E m) :
    operatorMatrix A.adjoint = (operatorMatrix A).conjTranspose := by
  dsimp only [operatorMatrix]
  rw [← ContinuousLinearMap.adjoint_toLinearMap, LinearMap.toMatrix_adjoint]

/-- Normalize a positive principal coefficient to the trace by an invertible
linear change of variables. -/
theorem exists_linearized_trace_normalizer {m : ℕ} {A : E m →L[ℝ] E m}
    (hA : (operatorMatrix A).PosDef) :
    ∃ L : E m ≃L[ℝ] E m, ∀ B : E m →L[ℝ] E m,
      linearizedTrace A B = (operatorMatrix (L.toContinuousLinearMap.adjoint.comp
        (B.comp L.toContinuousLinearMap))).trace := by
  let S := (operatorMatrix A)⁻¹
  let R := CFC.sqrt S
  have hR : R.IsHermitian := (CFC.sqrt_nonneg S).isSelfAdjoint
  have hRR : R * R = S := CFC.sqrt_mul_sqrt_self S hA.inv.posSemidef.nonneg
  have hu : IsUnit R := (CFC.isUnit_sqrt_iff S hA.inv.posSemidef.nonneg).mpr hA.inv.isUnit
  let b := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
  let l : E m →ₗ[ℝ] E m := Matrix.toLinAlgEquiv b R
  have hlu : IsUnit l := hu.map (Matrix.toLinAlgEquiv b).toMonoidHom
  have hl : Function.Bijective l := (Module.End.isUnit_iff l).mp hlu
  let L : E m ≃L[ℝ] E m := (LinearEquiv.ofBijective l hl).toContinuousLinearEquiv
  have hmat : operatorMatrix L.toContinuousLinearMap = R := by
    change LinearMap.toMatrix b b l = R
    exact LinearMap.toMatrixAlgEquiv_toLinAlgEquiv b R
  refine ⟨L, ?_⟩
  intro B
  calc
    linearizedTrace A B = Matrix.trace (S * operatorMatrix B) := rfl
    _ = Matrix.trace (R * operatorMatrix B * R) := by rw [Matrix.trace_mul_cycle, hRR]
    _ = _ := by
      rw [operatorMatrix_comp, operatorMatrix_comp, operatorMatrix_adjoint, hmat, hR.eq, Matrix.mul_assoc]

end Submission.Obl.Entropy__smooth_gaussian_transport
