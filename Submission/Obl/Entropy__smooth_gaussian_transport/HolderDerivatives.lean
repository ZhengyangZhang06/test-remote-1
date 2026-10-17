import Submission.Obl.Entropy__smooth_gaussian_transport.HolderFiniteDimension

open Set Filter Asymptotics
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem holderRegularAt_clm_apply_iff {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : X → Y →L[ℝ] Z} {n : ℕ} {α : ℝ} {x : X}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    HolderRegularAt n α f x ↔ ∀ v, HolderRegularAt n α (fun y => f y v) x := by
  refine ⟨fun hf v => hf.mapCLM hα hα1 (ContinuousLinearMap.apply ℝ Z v), fun h => ?_⟩
  have hc : ContDiffAt ℝ n f x := contDiffAt_clm_apply_iff.mpr (fun v => (h v).contDiffAt)
  refine ⟨hc, ?_⟩
  have hflip : UniformHolderAt α (fun y => (iteratedFDeriv ℝ n f y).flipLinear) x := by
    apply UniformHolderAt.clm_apply_iff.mpr
    intro v
    apply (h v).holder.congr
    filter_upwards [hc.eventually (by simp)] with y hy
    have he := (ContinuousLinearMap.apply ℝ Z v).iteratedFDeriv_comp_left hy le_rfl
    change iteratedFDeriv ℝ n (fun z => f z v) y = _ at he
    rw [he]
    apply ContinuousMultilinearMap.ext
    intro w
    rfl
  have hb : (fun p : X × X => iteratedFDeriv ℝ n f p.1 - iteratedFDeriv ℝ n f p.2)
      =O[nhds (x, x)] (fun p => (iteratedFDeriv ℝ n f p.1).flipLinear - (iteratedFDeriv ℝ n f p.2).flipLinear) := by
    apply Asymptotics.IsBigO.of_bound 1
    apply Filter.Eventually.of_forall
    intro p
    rw [one_mul]
    let T := (iteratedFDeriv ℝ n f p.1).flipLinear - (iteratedFDeriv ℝ n f p.2).flipLinear
    apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg T)
    intro w
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    change ‖T v w‖ ≤ _
    calc
      _ ≤ ‖T v‖ * ∏ i, ‖w i‖ := (T v).le_opNorm w
      _ ≤ (‖T‖ * ‖v‖) * ∏ i, ‖w i‖ := mul_le_mul_of_nonneg_right
        (T.le_opNorm v) (Finset.prod_nonneg (fun i _ => norm_nonneg _))
      _ = _ := by ring
  exact hb.trans hflip

theorem HolderRegularAt.of_fderiv {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {n : ℕ} {α : ℝ} {x : X}
    (hd : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y)
    (hf : HolderRegularAt n α (_root_.fderiv ℝ f) x) : HolderRegularAt (n + 1) α f x := by
  refine ⟨(contDiffAt_succ_iff_hasFDerivAt (n := n)).mpr
    ⟨_root_.fderiv ℝ f, ⟨_, hd, fun y hy => hy.hasFDerivAt⟩, hf.contDiffAt⟩, ?_⟩
  have h := hf.holder.mapCLM (continuousMultilinearCurryRightEquiv' ℝ n X Y).symm.toContinuousLinearEquiv.toContinuousLinearMap
  convert! h using 1
  funext y
  exact iteratedFDeriv_succ_eq_comp_right

theorem HolderRegularAt.of_directional_derivatives {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {n : ℕ} {α : ℝ} {x : X}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hd : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y)
    (hf : ∀ v, HolderRegularAt n α (fun y => _root_.fderiv ℝ f y v) x) :
    HolderRegularAt (n + 1) α f x :=
  .of_fderiv hd ((holderRegularAt_clm_apply_iff hα hα1).mpr hf)

end Submission.Obl.Entropy__smooth_gaussian_transport
