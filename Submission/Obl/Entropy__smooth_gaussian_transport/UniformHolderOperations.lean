import Submission.Obl.Entropy__smooth_gaussian_transport.UniformHolderAt

open Set Filter Asymptotics
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem UniformHolderAt.congr {X Y : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {α : ℝ} {f g : X → Y} {x : X} (hf : UniformHolderAt α f x) (he : f =ᶠ[nhds x] g) :
    UniformHolderAt α g x := by
  apply EventuallyEq.trans_isBigO _ hf
  filter_upwards [prod_mem_nhds he he] with p hp
  exact congrArg₂ (· - ·) hp.1.symm hp.2.symm

theorem UniformHolderAt.mapCLM {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {α : ℝ} {f : X → Y} {x : X} (hf : UniformHolderAt α f x) (L : Y →L[ℝ] Z) :
    UniformHolderAt α (fun y => L (f y)) x := by
  have h : (fun p : X × X => L (f p.1) - L (f p.2)) =O[nhds (x, x)]
      (fun p => f p.1 - f p.2) := by
    apply Asymptotics.IsBigO.of_bound ‖L‖
    exact Filter.Eventually.of_forall (fun p => by rw [← map_sub]; exact L.le_opNorm _)
  exact h.trans hf

theorem UniformHolderAt.smooth_comp {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {α : ℝ} {f : X → Y} {g : Y → Z} {x : X}
    (hf : UniformHolderAt α f x) (hfc : ContinuousAt f x) (hg : ContDiffAt ℝ 1 g (f x)) :
    UniformHolderAt α (fun y => g (f y)) x := by
  obtain ⟨L, U, hU, hLip⟩ := hg.exists_lipschitzOnWith
  have hnear := hfc.preimage_mem_nhds hU
  have h : (fun p : X × X => g (f p.1) - g (f p.2)) =O[nhds (x, x)]
      (fun p => f p.1 - f p.2) := by
    apply Asymptotics.IsBigO.of_bound L
    filter_upwards [prod_mem_nhds hnear hnear] with p hp
    simpa only [dist_eq_norm] using hLip.dist_le_mul _ hp.1 _ hp.2
  exact h.trans hf

theorem UniformHolderAt.prodMk {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    {α : ℝ} {f : X → Y} {g : X → Z} {x : X}
    (hf : UniformHolderAt α f x) (hg : UniformHolderAt α g x) :
    UniformHolderAt α (fun y => (f y, g y)) x := hf.prod_left hg

theorem UniformHolderAt.add {X Y : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {α : ℝ} {f g : X → Y} {x : X}
    (hf : UniformHolderAt α f x) (hg : UniformHolderAt α g x) :
    UniformHolderAt α (fun y => f y + g y) x := by
  have he (p : X × X) : (f p.1 + g p.1) - (f p.2 + g p.2) =
      (f p.1 - f p.2) + (g p.1 - g p.2) := by abel
  simpa only [UniformHolderAt, he] using Asymptotics.IsBigO.add hf hg

end Submission.Obl.Entropy__smooth_gaussian_transport
