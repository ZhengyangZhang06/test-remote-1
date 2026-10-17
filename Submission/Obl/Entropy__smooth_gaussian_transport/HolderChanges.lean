import Submission.Obl.Entropy__smooth_gaussian_transport.HolderComposition

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem UniformBoundedHolder.lower_exponent {ι X Y : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {α β : ℝ} {f : ι → X → Y} (hf : UniformBoundedHolder α f)
    (hβ : 0 ≤ β) (hβα : β ≤ α) : UniformBoundedHolder β f := by
  obtain ⟨M, C, hM, hC, hb, hm⟩ := hf
  refine ⟨M, C + 2 * M, hM, by positivity, hb, ?_⟩
  intro i x y
  have hp := Real.rpow_nonneg (norm_nonneg (x - y)) β
  by_cases hd : ‖x - y‖ ≤ 1
  · have he := Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg (x - y)) hd hβ hβα
    exact (hm i x y).trans ((mul_le_mul_of_nonneg_left he hC).trans (by nlinarith))
  · have he : 1 ≤ ‖x - y‖ ^ β := Real.one_le_rpow (le_of_not_ge hd) hβ
    have hn : ‖f i x - f i y‖ ≤ 2 * M := (norm_sub_le _ _).trans (by linarith [hb i x, hb i y])
    exact hn.trans (by nlinarith)

theorem UniformBoundedHolder.comp_lipschitz_domain {ι X Y Z : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    {α : ℝ} {f : ι → Y → Z} (hf : UniformBoundedHolder α f) (hα : 0 ≤ α)
    {g : X → Y} {L : NNReal} (hg : LipschitzWith L g) :
    UniformBoundedHolder α (fun i x => f i (g x)) := by
  obtain ⟨M, C, hM, hC, hb, hm⟩ := hf
  refine ⟨M, C * (L : ℝ) ^ α, hM, by positivity, fun i x => hb i _, ?_⟩
  intro i x y
  have hd : ‖g x - g y‖ ≤ (L : ℝ) * ‖x - y‖ := by
    simpa only [dist_eq_norm] using hg.dist_le_mul x y
  calc
    _ ≤ C * ‖g x - g y‖ ^ α := hm i _ _
    _ ≤ C * ((L : ℝ) * ‖x - y‖) ^ α := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hd hα) hC
    _ = _ := by rw [Real.mul_rpow L.coe_nonneg (norm_nonneg _)]; ring

end Submission.Obl.Entropy__smooth_gaussian_transport
