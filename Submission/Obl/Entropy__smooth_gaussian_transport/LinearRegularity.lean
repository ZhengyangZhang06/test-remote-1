import Submission.Obl.Entropy__smooth_gaussian_transport.LinearBootstrap
import Submission.Obl.Entropy__smooth_gaussian_transport.NormalizedCoefficients

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem linear_schauder_bootstrap {m : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (n : ℕ) {f g : E m → ℝ} {A : E m → (E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ} {x : E m}
    (hf : HolderRegularAt 2 α f x) (hg : HolderRegularAt n α g x) (hA : HolderRegularAt n α A x)
    (hnormal : ∃ L : E m ≃L[ℝ] E m, ∀ B, A x (untransformHessian L B) = hessianTrace m B)
    (heq : ∀ᶠ y in nhds x, A y (iteratedFDeriv ℝ 2 f y) = g y) :
    HolderRegularAt (n + 2) α f x := by
  obtain ⟨L, hL⟩ := hnormal
  let z := L.symm x
  let J : ((E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ) →L[ℝ] ((E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (E m [×2]→L[ℝ] ℝ) (E m [×2]→L[ℝ] ℝ) ℝ).flip (untransformHessian L)
  have hf' : HolderRegularAt 2 α (fun y => f (L y)) z := by
    apply HolderRegularAt.comp_linearEquiv hα.le L z
    simpa only [z, L.apply_symm_apply] using hf
  have hg' : HolderRegularAt n α (fun y => g (L y)) z := by
    apply HolderRegularAt.comp_linearEquiv hα.le L z
    simpa only [z, L.apply_symm_apply] using hg
  have hA' : HolderRegularAt n α (fun y => J (A (L y))) z := by
    have hcomp : HolderRegularAt n α (fun y => A (L y)) z := by
      apply HolderRegularAt.comp_linearEquiv hα.le L z
      simpa only [z, L.apply_symm_apply] using hA
    exact HolderRegularAt.mapCLM (Y := (E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ)
      (Z := (E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ) hcomp hα.le hα1.le J
  have hbase : J (A (L z)) = hessianTrace m := by
    apply ContinuousLinearMap.ext
    intro B
    change A (L z) (untransformHessian L B) = _
    simpa only [z, L.apply_symm_apply] using hL B
  have heq' : ∀ᶠ y in nhds z, J (A (L y)) (iteratedFDeriv ℝ 2 (fun w => f (L w)) y) = g (L y) := by
    have hlim : Tendsto L (nhds z) (nhds x) := by simpa only [z, L.apply_symm_apply] using L.continuous.tendsto z
    filter_upwards [hlim.eventually heq] with y hy
    change A (L y) (untransformHessian L (iteratedFDeriv ℝ 2 (fun w => f (L w)) y)) = _
    rw [iteratedFDeriv_comp_equiv, untransformHessian_comp]
    exact hy
  have hreg := normalized_linear_schauder_bootstrap hα hα1 n hf' hg' hA' hbase heq'
  have hout := hreg.comp_linearEquiv hα.le L.symm x
  convert! hout using 1
  funext y
  exact congrArg f (L.apply_symm_apply y).symm

end Submission.Obl.Entropy__smooth_gaussian_transport
