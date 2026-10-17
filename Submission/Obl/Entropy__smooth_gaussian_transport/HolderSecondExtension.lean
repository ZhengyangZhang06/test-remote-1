import Submission.Obl.Entropy__smooth_gaussian_transport.HolderFirstExtension
import Submission.Obl.Entropy__smooth_gaussian_transport.CompactHolderExtension

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem HolderRegularAt.exists_second_extension {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {f : X → ℝ} {x : X} {α : ℝ} (hf : HolderRegularAt 2 α f x)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ g : X → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ g =ᶠ[nhds x] f ∧
      UniformBoundedHolder α (fun (_ : Unit) => iteratedFDeriv ℝ 2 g) := by
  obtain ⟨f₀, hreg, hfc, he⟩ := exists_compact_contDiff_extension hf.contDiffAt
  have hdf : UniformHolderAt α (iteratedFDeriv ℝ 2 f₀) x :=
    hf.holder.congr (he.symm.iteratedFDeriv ℝ 2)
  obtain ⟨r, C, hr, hC, hmod⟩ := hdf.exists_ball_bound
  obtain ⟨χ, hχ, hc, hs, hχrange, hone⟩ := exists_compact_smooth_cutoff
    (Metric.ball_mem_nhds x (by positivity : 0 < r / 3))
  obtain ⟨M, hM, hb⟩ := ((hfc.iteratedFDeriv 2).isCompact_range
    (hreg.continuous_iteratedFDeriv le_rfl)).isBounded.exists_pos_norm_le
  have hthick : ∀ y ∈ tsupport χ, ∀ z, ‖y - z‖ < r / 3 → z ∈ Metric.ball x r := by
    intro y hy z hz
    have hy' : ‖y - x‖ < r / 3 := by simpa only [Metric.mem_ball, dist_eq_norm] using hs hy
    rw [Metric.mem_ball, dist_eq_norm]
    have he : z - x = (z - y) + (y - x) := by abel
    rw [he]
    have hz' : ‖z - y‖ < r / 3 := by simpa only [norm_sub_rev] using hz
    exact (norm_add_le _ _).trans_lt (by linarith)
  have hmain : UniformBoundedHolder α (fun (_ : Unit) y => χ y • iteratedFDeriv ℝ 2 f₀ y) :=
    uniformBoundedHolder_cutoff_bilinear
      (hχ.of_le (WithTop.coe_le_coe.mpr (le_top : (1 : ENat) ≤ ⊤))) hc hα hα1
      (by positivity : 0 < r / 3) hM.le hC hthick (fun (_ : Unit) y _ => hb _ (mem_range_self y))
      (fun (_ : Unit) => hmod) (ContinuousLinearMap.lsmul ℝ ℝ)
  refine ⟨fun y => χ y * f₀ y,
    (hχ.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ENat) ≤ ⊤))).mul hreg,
    hc.mul_right, ?_, compact_hessian_holder_mul_of_cutoff hreg
      (hχ.of_le (WithTop.coe_le_coe.mpr (le_top : (3 : ENat) ≤ ⊤))) hc hα hα1 hmain⟩
  filter_upwards [hone, he] with y hy hey
  simp only [hy, one_mul, hey]

end Submission.Obl.Entropy__smooth_gaussian_transport
