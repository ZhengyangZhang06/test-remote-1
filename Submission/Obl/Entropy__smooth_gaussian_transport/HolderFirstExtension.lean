import Submission.Obl.Entropy__smooth_gaussian_transport.HolderDerivatives
import Submission.Obl.Entropy__smooth_gaussian_transport.FiniteSmoothExtension
import Submission.Obl.Entropy__smooth_gaussian_transport.HolderCutoff
import Submission.Obl.Entropy__smooth_gaussian_transport.QuotientBounds

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem compact_bilinear_left_support {X Y Z W : Type*}
    [TopologicalSpace X] [T2Space X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : X → Y} {g : X → Z} (hf : HasCompactSupport f) (B : Y →L[ℝ] Z →L[ℝ] W) :
    HasCompactSupport (fun x => B (f x) (g x)) := by
  apply HasCompactSupport.of_support_subset_isCompact hf
  intro x hx
  apply subset_closure
  contrapose! hx
  rw [Function.notMem_support] at hx ⊢
  simp only [hx, map_zero, zero_apply]

theorem HolderRegularAt.exists_first_extension {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {x : X} {α : ℝ} (hf : HolderRegularAt 1 α f x)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ g : X → Y, ContDiff ℝ 1 g ∧ HasCompactSupport g ∧ g =ᶠ[nhds x] f ∧
      UniformDerivativeHolder α g := by
  obtain ⟨f₀, hreg, hfc, he⟩ := exists_compact_contDiff_extension hf.contDiffAt
  have hdf : UniformHolderAt α (_root_.fderiv ℝ f₀) x := by
    exact (holderRegularAt_zero_iff.mp hf.fderiv).2.congr (he.symm.fderiv (𝕜 := ℝ))
  obtain ⟨r, C, hr, hC, hmod⟩ := hdf.exists_ball_bound
  obtain ⟨χ, hχ, hc, hs, hχrange, hone⟩ := exists_compact_smooth_cutoff
    (Metric.ball_mem_nhds x (by positivity : 0 < r / 3))
  obtain ⟨M, hM, hb⟩ := ((hfc.fderiv ℝ).isCompact_range
    (hreg.continuous_fderiv (by norm_num))).isBounded.exists_pos_norm_le
  have hthick : ∀ y ∈ tsupport χ, ∀ z, ‖y - z‖ < r / 3 → z ∈ Metric.ball x r := by
    intro y hy z hz
    have hy' : ‖y - x‖ < r / 3 := by simpa only [Metric.mem_ball, dist_eq_norm] using hs hy
    rw [Metric.mem_ball, dist_eq_norm]
    have he : z - x = (z - y) + (y - x) := by abel
    rw [he]
    have hz' : ‖z - y‖ < r / 3 := by simpa only [norm_sub_rev] using hz
    exact (norm_add_le _ _).trans_lt (by linarith)
  have hmain : UniformBoundedHolder α (fun (_ : Unit) y => χ y • _root_.fderiv ℝ f₀ y) :=
    uniformBoundedHolder_cutoff_bilinear
      (hχ.of_le (WithTop.coe_le_coe.mpr (le_top : (1 : ENat) ≤ ⊤))) hc hα hα1
      (by positivity : 0 < r / 3) hM.le hC hthick (fun (_ : Unit) y _ => hb _ (mem_range_self y))
      (fun (_ : Unit) => hmod) (ContinuousLinearMap.lsmul ℝ ℝ)
  have hother : UniformBoundedHolder α (fun (_ : Unit) y => (_root_.fderiv ℝ χ y).smulRight (f₀ y)) :=
    .of_compact_c1 ((hχ.fderiv_right (by change ((2 : ENat) : WithTop ENat) ≤ _; exact WithTop.coe_le_coe.mpr le_top)).smulRight hreg)
      (compact_bilinear_left_support (hc.fderiv ℝ) (ContinuousLinearMap.smulRightL ℝ X Y)) hα hα1
  refine ⟨fun y => χ y • f₀ y, (hχ.of_le (WithTop.coe_le_coe.mpr (le_top : (1 : ENat) ≤ ⊤))).smul hreg,
    hc.smul_right, ?_, ?_⟩
  · filter_upwards [hone, he] with y hy hey
    simp only [hy, one_smul, hey]
  · change UniformBoundedHolder α (fun (_ : Unit) => _root_.fderiv ℝ (fun y => χ y • f₀ y))
    convert! hmain.add hother using 1
    funext i y
    exact ((hχ.differentiable (by simp) y).hasFDerivAt.smul (hreg.differentiable_one y).hasFDerivAt).fderiv

end Submission.Obl.Entropy__smooth_gaussian_transport
