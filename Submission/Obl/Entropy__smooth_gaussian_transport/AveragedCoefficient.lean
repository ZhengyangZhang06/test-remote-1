import Submission.Obl.Entropy__smooth_gaussian_transport.SmallCoefficientExtension
import Submission.Obl.Entropy__smooth_gaussian_transport.HolderComposition

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem exists_uniform_small_averaged_coefficient {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    {H : X → Y} {P : Y → Z} {x : X} {α ε : ℝ}
    (hH : ContinuousAt H x) (hmod : UniformBoundedHolder α (fun (_ : Unit) => H))
    (hP : ContDiffAt ℝ 1 P (H x)) (hPx : P (H x) = 0) (hε : 0 < ε) :
    ∃ T : X → X → Z, UniformBoundedHolder α T ∧ (∀ h z, ‖T h z‖ ≤ ε) ∧
      ∃ r : ℝ, 0 < r ∧ ∀ h z, ‖h‖ < r → ‖z - x‖ < r →
        T h z = segmentMean P (H z) (H (z + h)) := by
  obtain ⟨P₀, ⟨L, hLip⟩, hsmall, he⟩ := exists_small_lipschitz_extension hP hPx hε
  let T : X → X → Z := fun h z => segmentMean P₀ (H z) (H (z + h))
  have hH' : UniformBoundedHolder α (fun (_ : X) => H) := hmod.reindex (fun _ => ())
  refine ⟨T, hH'.segmentMean (hH'.translate (fun h => h)) hLip, ?_, ?_⟩
  · intro h z
    exact interval_average_norm_bound (fun t ht => hsmall _)
  · obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp he
    have hnear : {z | H z ∈ Metric.ball (H x) ρ} ∈ nhds x :=
      hH.preimage_mem_nhds (Metric.ball_mem_nhds _ hρ)
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
    refine ⟨δ / 3, by positivity, ?_⟩
    intro h z hh hz
    have hzδ : z ∈ Metric.ball x δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      linarith
    have hzhδ : z + h ∈ Metric.ball x δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have he : z + h - x = (z - x) + h := by abel
      rw [he]
      exact (norm_add_le _ _).trans_lt (by linarith)
    change (∫ t in (0 : ℝ)..1, P₀ ((1 - t) • H z + t • H (z + h))) = _
    unfold segmentMean
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    apply hρsub
    exact (convex_ball (H x) ρ) (hδsub hzδ) (hδsub hzhδ)
      (sub_nonneg.mpr ht'.2) ht'.1 (by ring)

end Submission.Obl.Entropy__smooth_gaussian_transport
