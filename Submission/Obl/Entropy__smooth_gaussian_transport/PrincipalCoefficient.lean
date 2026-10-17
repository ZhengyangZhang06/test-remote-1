import Submission.Obl.Entropy__smooth_gaussian_transport.HessianOperators
import Submission.Obl.Entropy__smooth_gaussian_transport.CoefficientHolder

open Set
open scoped Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem principalHessian_contDiffAt {m : ℕ} {n : WithTop ENat} {A : E m →L[ℝ] E m}
    (hA : A.det ≠ 0) : ContDiffAt ℝ n (principalHessian (m := m)) A := by
  letI : FiniteDimensional ℝ (E m [×2]→L[ℝ] ℝ) :=
    FiniteDimensional.of_injective (hessianCurry (E m) ℝ).toLinearEquiv.toLinearMap
      (hessianCurry (E m) ℝ).injective
  let S : Set (E m →L[ℝ] E m) := {B | B.det ≠ 0}
  have hS : IsOpen S := isOpen_ne.preimage ContinuousLinearMap.continuous_det
  have hreg : ContDiffOn ℝ n (principalHessian (m := m)) S := by
    apply contDiffOn_clm_apply.mpr
    intro B C hC
    have hh : ContDiffAt ℝ n (fun z : E m →L[ℝ] E m =>
        linearizedTrace z (hessianOperator m B)) C :=
      ContDiffAt.comp C (f := fun z : E m →L[ℝ] E m => (z, hessianOperator m B))
        (linearizedTrace_contDiffAt (n := n) (A := C) (B := hessianOperator m B) hC)
        (contDiff_id.prodMk contDiff_const).contDiffAt
    exact hh.contDiffWithinAt
  exact hreg.contDiffAt (hS.mem_nhds hA)

theorem compact_principalHessian_lipschitz {m : ℕ} {S : Set (E m →L[ℝ] E m)}
    (hS : IsCompact S) (hdet : ∀ A ∈ S, A.det ≠ 0) :
    ∃ C : NNReal, LipschitzOnWith C (principalHessian (m := m)) S :=
  compact_c1_lipschitz hS (fun A hA => principalHessian_contDiffAt (hdet A hA))

end Submission.Obl.Entropy__smooth_gaussian_transport
