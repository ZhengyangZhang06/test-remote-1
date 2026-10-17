import Submission.Obl.Entropy__smooth_gaussian_transport.HolderLocalization

open Set

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem compact_c1_lipschitz_global {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ L : NNReal, LipschitzWith L f := by
  obtain ⟨L, hL, hD⟩ := ((hc.fderiv ℝ).isCompact_range
    (hf.continuous_fderiv (by norm_num))).isBounded.exists_pos_norm_le
  exact ⟨⟨L, hL.le⟩, lipschitzWith_of_nnnorm_fderiv_le hf.differentiable_one
    (fun y => by exact_mod_cast hD _ (mem_range_self y))⟩

end Submission.Obl.Entropy__smooth_gaussian_transport
