import Submission.Obl.Entropy__smooth_gaussian_transport.CompactHolderExtension
import Submission.Obl.Entropy__smooth_gaussian_transport.HolderChanges
import Submission.Obl.Entropy__smooth_gaussian_transport.HessianReconstruction

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem exists_compact_hessian_holder_extension {m : ℕ} {f : E m → ℝ}
    (hf : ContDiff ℝ 2 f) (x : E m) {α C : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    (hmod : ∀ y ∈ Metric.closedBall x 2, ∀ z ∈ Metric.closedBall x 2,
      ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ C * ‖y - z‖ ^ α) :
    ∃ g : E m → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ g =ᶠ[nhds x] f ∧
      UniformBoundedHolder α (fun (_ : Unit) => iteratedFDeriv ℝ 2 g) := by
  let χ : ContDiffBump x := { rIn := 1 / 2, rOut := 1, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  have hc : IsCompact (Metric.closedBall x (2 : ℝ)) := isCompact_closedBall _ _
  obtain ⟨M, hM, hb⟩ := (hc.image (show Continuous (iteratedFDeriv ℝ 2 f) from hf.continuous_iteratedFDeriv le_rfl)).isBounded.exists_pos_norm_le
  have hthick : ∀ y ∈ tsupport χ, ∀ z, ‖y - z‖ < 1 → z ∈ Metric.closedBall x 2 := by
    intro y hy z hz
    rw [χ.tsupport_eq, Metric.mem_closedBall, dist_eq_norm] at hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    have he : z - x = (z - y) + (y - x) := by abel
    rw [he]
    have hzy : ‖z - y‖ < 1 := by simpa only [norm_sub_rev] using hz
    exact (norm_add_le _ _).trans (by dsimp only [χ] at hy; linarith)
  have hmain : UniformBoundedHolder α (fun (_ : Unit) y => χ y • iteratedFDeriv ℝ 2 f y) :=
    uniformBoundedHolder_cutoff_bilinear (χ.contDiff (n := 1)) χ.hasCompactSupport hα hα1
      (by norm_num : (0 : ℝ) < 1) hM.le hC hthick
      (fun (_ : Unit) y hy => hb _ (mem_image_of_mem _ hy)) (fun (_ : Unit) => hmod)
      (ContinuousLinearMap.lsmul ℝ ℝ)
  refine ⟨fun y => χ y * f y, χ.contDiff.mul hf, χ.hasCompactSupport.mul_right, ?_,
    compact_hessian_holder_mul_of_cutoff (f := f) hf (χ.contDiff (n := 3)) χ.hasCompactSupport hα hα1 hmain⟩
  filter_upwards [χ.eventuallyEq_one] with y hy
  simp only [hy, Pi.one_apply, one_mul]

theorem compact_hessian_holder_of_operator_holder {m : ℕ} {f : E m → ℝ}
    (hf : ContDiff ℝ 2 f) {K : Set (E m)} {α C : ℝ} (hC : 0 ≤ C)
    (hmod : ∀ x ∈ K, ∀ y ∈ K,
      ‖fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) x‖ ≤ C * ‖y - x‖ ^ α) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ K, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ D * ‖x - y‖ ^ α := by
  refine ⟨‖hessianOfOperator m‖ * C, by positivity, ?_⟩
  intro x hx y hy
  rw [← hessianOfOperator_fderiv_gradient hf x, ← hessianOfOperator_fderiv_gradient hf y, ← map_sub]
  exact ((hessianOfOperator m).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left (hmod y hy x hx) (norm_nonneg _)).trans_eq (by ring))

end Submission.Obl.Entropy__smooth_gaussian_transport
