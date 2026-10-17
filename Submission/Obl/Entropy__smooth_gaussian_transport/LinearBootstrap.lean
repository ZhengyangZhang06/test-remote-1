import Submission.Obl.Entropy__smooth_gaussian_transport.LocalLinearStep
import Submission.Obl.Entropy__smooth_gaussian_transport.HolderHigherJets
import Submission.Obl.Entropy__smooth_gaussian_transport.DifferentiateEquation

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem normalized_linear_schauder_bootstrap {m : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (n : ℕ) {f g : E m → ℝ} {A : E m → (E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ} {x : E m}
    (hf : HolderRegularAt 2 α f x) (hg : HolderRegularAt n α g x) (hA : HolderRegularAt n α A x)
    (hAx : A x = hessianTrace m)
    (heq : ∀ᶠ y in nhds x, A y (iteratedFDeriv ℝ 2 f y) = g y) :
    HolderRegularAt (n + 2) α f x := by
  induction n generalizing f g A x with
  | zero => exact hf
  | succ n ih =>
    have hfn : HolderRegularAt (n + 2) α f x := ih hf
      (hg.of_order_le hα.le hα1.le (Nat.le_succ n)) (hA.of_order_le hα.le hα1.le (Nat.le_succ n)) hAx heq
    have hf3 : HolderRegularAt 3 α f x := local_normalized_linear_regularity hα hα1 hf
      (hg.of_order_le hα.le hα1.le (Nat.succ_le_succ (Nat.zero_le n)))
      (hA.of_order_le hα.le hα1.le (Nat.succ_le_succ (Nat.zero_le n))) hAx heq
    have hH : HolderRegularAt n α (iteratedFDeriv ℝ 2 f) x := hfn.iteratedFDeriv hα.le hα1.le
    apply HolderRegularAt.of_directional_derivatives hα.le hα1.le
      (hf.contDiffAt.eventually (by simp) |>.mono (fun y hy => hy.differentiableAt (by norm_num)))
    intro v
    let u : E m → ℝ := fun y => fderiv ℝ f y v
    let G : E m → ℝ := fun y => fderiv ℝ g y v - fderiv ℝ A y v (iteratedFDeriv ℝ 2 f y)
    have hu : HolderRegularAt 2 α u x := hf3.fderiv.mapCLM hα.le hα1.le (ContinuousLinearMap.apply ℝ ℝ v)
    have hG : HolderRegularAt n α G x :=
      (hg.fderiv.mapCLM hα.le hα1.le (ContinuousLinearMap.apply ℝ ℝ v)).sub
        ((hA.fderiv.mapCLM hα.le hα1.le
          (ContinuousLinearMap.apply ℝ ((E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ) v)).clm_apply hH hα.le hα1.le)
        hα.le hα1.le
    have hloc : ∀ᶠ y in nhds x, A y (iteratedFDeriv ℝ 2 u y) = G y := by
      have hAf : ContDiffAt ℝ 1 A x := hA.contDiffAt.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      have hgf : ContDiffAt ℝ 1 g x := hg.contDiffAt.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      filter_upwards [hf3.contDiffAt.eventually (by simp), hAf.eventually (by simp), hgf.eventually (by simp),
        eventually_eventually_nhds.mpr heq] with y hyf hyA hyg hye
      exact differentiate_linear_equation hyf hyg.differentiableAt_one hyA.differentiableAt_one hye v
    exact ih hu hG (hA.of_order_le hα.le hα1.le (Nat.le_succ n)) hAx hloc

end Submission.Obl.Entropy__smooth_gaussian_transport
