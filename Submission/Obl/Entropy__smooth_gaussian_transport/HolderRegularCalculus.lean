import Submission.Obl.Entropy__smooth_gaussian_transport.UniformHolderOperations

open Set Filter Asymptotics
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem HolderRegularAt.of_contDiffAt {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {x : X} {n : ℕ} {α : ℝ}
    (hf : ContDiffAt ℝ (n + 1) f x) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    HolderRegularAt n α f x := by
  refine ⟨hf.of_le (by exact_mod_cast Nat.le_succ n), ?_⟩
  apply UniformHolderAt.of_contDiffAt_one _ hα hα1
  exact hf.iteratedFDeriv_right (by simp [add_comm])

theorem HolderRegularAt.of_order_le {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {x : X} {n k : ℕ} {α : ℝ}
    (hf : HolderRegularAt n α f x) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hk : k ≤ n) :
    HolderRegularAt k α f x := by
  rcases lt_or_eq_of_le hk with hlt | rfl
  · exact .of_contDiffAt (hf.contDiffAt.of_le (by exact_mod_cast Nat.add_one_le_iff.mpr hlt)) hα hα1
  · exact hf

theorem holderRegularAt_zero_iff {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {x : X} {α : ℝ} :
    HolderRegularAt 0 α f x ↔ ContDiffAt ℝ 0 f x ∧ UniformHolderAt α f x := by
  constructor
  · intro hf
    refine ⟨hf.contDiffAt, ?_⟩
    apply Asymptotics.IsBigO.of_norm_left
    simpa only [UniformHolderAt, iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
      LinearIsometryEquiv.norm_map] using hf.holder.norm_left
  · rintro ⟨hc, hh⟩
    refine ⟨hc, ?_⟩
    apply Asymptotics.IsBigO.of_norm_left
    simpa only [UniformHolderAt, iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
      LinearIsometryEquiv.norm_map] using hh.norm_left

theorem HolderRegularAt.fderiv {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {x : X} {n : ℕ} {α : ℝ}
    (hf : HolderRegularAt (n + 1) α f x) : HolderRegularAt n α (_root_.fderiv ℝ f) x := by
  refine ⟨hf.contDiffAt.fderiv_right (by simp), ?_⟩
  apply Asymptotics.IsBigO.of_norm_left
  have he (y z : X) : ‖iteratedFDeriv ℝ (n + 1) f y - iteratedFDeriv ℝ (n + 1) f z‖ =
      ‖iteratedFDeriv ℝ n (_root_.fderiv ℝ f) y - iteratedFDeriv ℝ n (_root_.fderiv ℝ f) z‖ := by
    rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
    change ‖(continuousMultilinearCurryRightEquiv' ℝ n X Y).symm _ -
      (continuousMultilinearCurryRightEquiv' ℝ n X Y).symm _‖ = _
    rw [← (continuousMultilinearCurryRightEquiv' ℝ n X Y).symm.map_sub,
      (continuousMultilinearCurryRightEquiv' ℝ n X Y).symm.norm_map]
  simpa only [he] using hf.holder.norm_left

theorem HolderRegularAt.prodMk {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : X → Y} {g : X → Z} {x : X} {n : ℕ} {α : ℝ}
    (hf : HolderRegularAt n α f x) (hg : HolderRegularAt n α g x) :
    HolderRegularAt n α (fun y => (f y, g y)) x := by
  refine ⟨hf.contDiffAt.prodMk hg.contDiffAt, ?_⟩
  have he : (fun p : X × X => iteratedFDeriv ℝ n (fun y => (f y, g y)) p.1 -
      iteratedFDeriv ℝ n (fun y => (f y, g y)) p.2) =ᶠ[nhds (x, x)]
      (fun p => (iteratedFDeriv ℝ n f p.1 - iteratedFDeriv ℝ n f p.2).prod
        (iteratedFDeriv ℝ n g p.1 - iteratedFDeriv ℝ n g p.2)) := by
    have hn := (hf.contDiffAt.eventually (by simp)).and (hg.contDiffAt.eventually (by simp))
    filter_upwards [prod_mem_nhds hn hn] with p hp
    apply DFunLike.ext
    rw [iteratedFDeriv_prodMk hp.1.1 hp.1.2 le_rfl, iteratedFDeriv_prodMk hp.2.1 hp.2.2 le_rfl]
    intro v
    rfl
  apply he.trans_isBigO
  apply Asymptotics.IsBigO.of_norm_left
  simp only [ContinuousMultilinearMap.opNorm_prod, ← Prod.norm_mk]
  exact (hf.holder.prod_left hg.holder).norm_left

theorem HolderRegularAt.comp_smooth {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : X → Y} {g : Y → Z} {x : X} {n : ℕ} {α : ℝ}
    (hf : HolderRegularAt n α f x) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hg : ContDiffAt ℝ (n + 1) g (f x)) : HolderRegularAt n α (g ∘ f) x := by
  have hgn : ContDiffAt ℝ n g (f x) := hg.of_le (by exact_mod_cast Nat.le_succ n)
  refine ⟨hgn.comp x hf.contDiffAt, ?_⟩
  have he : (fun p : X × X => iteratedFDeriv ℝ n (g ∘ f) p.1 - iteratedFDeriv ℝ n (g ∘ f) p.2)
      =ᶠ[nhds (x, x)] (fun p => (ftaylorSeries ℝ g (f p.1)).taylorComp (ftaylorSeries ℝ f p.1) n -
        (ftaylorSeries ℝ g (f p.2)).taylorComp (ftaylorSeries ℝ f p.2) n) := by
    have hn := (hf.contDiffAt.eventually (by simp)).and
      (hf.contDiffAt.continuousAt.eventually (hgn.eventually (by simp)))
    filter_upwards [prod_mem_nhds hn hn] with p hp
    rw [iteratedFDeriv_comp hp.1.2 hp.1.1 le_rfl, iteratedFDeriv_comp hp.2.2 hp.2.1 le_rfl]
  apply he.trans_isBigO
  apply FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO
  · intro i hi
    exact (((hgn.continuousAt_iteratedFDeriv (by exact_mod_cast hi)).comp hf.contDiffAt.continuousAt).comp
      (continuous_fst.continuousAt : ContinuousAt (Prod.fst : X × X → X) (x, x))).norm.isBoundedUnder_le
  · intro i hi
    have hfi : UniformHolderAt α f x := (holderRegularAt_zero_iff.mp (hf.of_order_le hα hα1 (Nat.zero_le _))).2
    exact hfi.smooth_comp hf.contDiffAt.continuousAt
      (hg.iteratedFDeriv_right (by exact_mod_cast (show 1 + i ≤ n + 1 by omega)))
  · intro i hi
    exact ((hf.contDiffAt.continuousAt_iteratedFDeriv (by exact_mod_cast hi)).comp
      (continuous_fst.continuousAt : ContinuousAt (Prod.fst : X × X → X) (x, x))).norm.isBoundedUnder_le
  · intro i hi
    exact ((hf.contDiffAt.continuousAt_iteratedFDeriv (by exact_mod_cast hi)).comp
      (continuous_snd.continuousAt : ContinuousAt (Prod.snd : X × X → X) (x, x))).norm.isBoundedUnder_le
  · intro i hi
    exact (hf.of_order_le hα hα1 hi).holder

end Submission.Obl.Entropy__smooth_gaussian_transport
