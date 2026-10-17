import Submission.Obl.Entropy__smooth_gaussian_transport.HolderSecondExtension
import Submission.Obl.Entropy__smooth_gaussian_transport.LinearQuotientStep

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem local_normalized_linear_regularity {m : ℕ} {f g : E m → ℝ}
    {A : E m → (E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ} {x : E m} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (hf : HolderRegularAt 2 α f x) (hg : HolderRegularAt 1 α g x)
    (hA : HolderRegularAt 1 α A x) (hAx : A x = hessianTrace m)
    (heq : ∀ᶠ y in nhds x, A y (iteratedFDeriv ℝ 2 f y) = g y) :
    HolderRegularAt 3 α f x := by
  obtain ⟨f₀, hf₀, hfc, hef, hH⟩ := hf.exists_second_extension hα hα1.le
  obtain ⟨g₀, hg₀, hgc, heg, hDg⟩ := hg.exists_first_extension hα hα1.le
  obtain ⟨A₀, hA₀, hAc, heA, hDA⟩ := hA.exists_first_extension hα hα1.le
  have hnear : ∀ᶠ y in nhds x, A₀ y (iteratedFDeriv ℝ 2 f₀ y) = g₀ y := by
    filter_upwards [heA, heg, hef.iteratedFDeriv ℝ 2, heq] with y hyA hyg hyf hye
    rw [hyA, hyf, hyg]
    exact hye
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hnear
  apply HolderRegularAt.of_directional_derivatives hα.le hα1.le
    (hf.contDiffAt.eventually (by simp) |>.mono (fun y hy => hy.differentiableAt (by norm_num)))
  intro v
  obtain ⟨χ, hone, hreg, hbound⟩ := linear_quotient_regularization hf₀ hfc hg₀ hA₀ hα hα1 hH hDg hDA
    x (heA.eq_of_nhds.trans hAx) hr
    (fun y hy => hsub (by simpa only [Metric.mem_ball, dist_eq_norm] using hy)) v
  have hloc : HolderRegularAt 2 α (fun y => χ y * fderiv ℝ f₀ y v) x := by
    refine ⟨hreg.contDiffAt, ?_⟩
    obtain ⟨M, C, hM, hC, hb, hm⟩ := hbound
    exact UniformHolderAt.of_bound (U := univ) univ_mem (fun y _ z _ => hm () y z)
  apply hloc.congr
  filter_upwards [hone, hef.fderiv (𝕜 := ℝ)] with y hy hyf
  simp only [hy, one_mul, hyf]

end Submission.Obl.Entropy__smooth_gaussian_transport
