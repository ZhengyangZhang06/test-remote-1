import Mathlib

open Set Filter
open scoped Topology

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem exists_small_holder_scale {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) (C : ℝ) :
    ∃ t : ℝ, 0 < t ∧ C * t ^ α < ε := by
  have hl : Tendsto (fun t : ℝ => C * t ^ α) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hα.ne', mul_zero] using
      ((Real.continuous_rpow_const hα.le).const_mul C).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, C * t ^ α < ε := hl.eventually (eventually_lt_nhds hε)
  have hp : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioi 0 := self_mem_nhdsWithin
  obtain ⟨t, ht, hs⟩ := Filter.Eventually.exists (Filter.Eventually.and hp he)
  exact ⟨t, ht, hs⟩

end Submission.Obl.Entropy__smooth_gaussian_transport
