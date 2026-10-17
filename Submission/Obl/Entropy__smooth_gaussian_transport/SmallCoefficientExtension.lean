import Submission.Obl.Entropy__smooth_gaussian_transport.SmoothExtension

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem exists_small_lipschitz_extension {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {x : X} (hf : ContDiffAt ℝ 1 f x) (hfx : f x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : X → Y, (∃ L : NNReal, LipschitzWith L g) ∧
      (∀ y, ‖g y‖ ≤ ε) ∧ g =ᶠ[nhds x] f := by
  obtain ⟨g₀, hg₀, hc₀, he₀⟩ := exists_compact_c1_extension hf
  have hgx : g₀ x = 0 := (he₀.eq_of_nhds).trans hfx
  have hU : {y | ‖g₀ y‖ < ε} ∈ nhds x := by
    have he : ‖g₀ x‖ < ε := by simpa only [hgx, norm_zero] using hε
    exact (isOpen_lt hg₀.continuous.norm continuous_const).mem_nhds he
  obtain ⟨χ, hχ, hχc, hχU, hrange, hone⟩ := exists_compact_smooth_cutoff hU
  let g : X → Y := fun y => χ y • g₀ y
  have hg : ContDiff ℝ 1 g := (hχ.of_le (by exact_mod_cast (le_top : (1 : ENat) ≤ ⊤))).smul hg₀
  have hc : HasCompactSupport g := hχc.smul_right
  obtain ⟨L, hL, hD⟩ := ((hc.fderiv ℝ).isCompact_range
    (hg.continuous_fderiv (by norm_num))).isBounded.exists_pos_norm_le
  refine ⟨g, ⟨⟨L, hL.le⟩, lipschitzWith_of_nnnorm_fderiv_le hg.differentiable_one
    (fun y => by exact_mod_cast hD _ (mem_range_self y))⟩, ?_, ?_⟩
  · intro y
    by_cases hy : χ y = 0
    · simpa only [g, hy, zero_smul, norm_zero] using hε.le
    · have hb : ‖g₀ y‖ ≤ ε := (hχU (subset_closure hy)).le
      simpa only [g, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hrange y).1] using
        (mul_le_mul (hrange y).2 hb (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul ε)
  · filter_upwards [hone, he₀] with y hy he
    simp only [g, hy, one_smul, he]

end Submission.Obl.Entropy__smooth_gaussian_transport
