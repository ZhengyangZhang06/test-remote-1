import Submission.Obl.Entropy__smooth_gaussian_transport.Brenier

open MeasureTheory ProbabilityTheory Set
open scoped ContDiff

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Positive continuous densities are bounded above and away from zero on compact sets. -/
theorem density_bounds_on_compact {m : ℕ} {f : E m → ℝ}
    (hf : Continuous f) (hp : ∀ x, 0 < f x) {s : Set (E m)} (hs : IsCompact s) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ x ∈ s, a ≤ f x ∧ f x ≤ b := by
  obtain ⟨a, ha, hax⟩ := hs.exists_forall_le' hf.continuousOn (fun x _ => hp x)
  obtain ⟨b, hb⟩ := hs.bddAbove_image hf.continuousOn
  exact ⟨a, max a b, ha, le_max_left _ _, fun x hx =>
    ⟨hax x hx, (hb (mem_image_of_mem f hx)).trans (le_max_right _ _)⟩⟩

theorem target_density_bounds {m : ℕ} {V : E m → ℝ} (hV : Continuous V)
    {s : Set (E m)} (hs : IsCompact s) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ x ∈ s, a ≤ Real.exp (-V x) ∧ Real.exp (-V x) ≤ b :=
  density_bounds_on_compact (Real.continuous_exp.comp hV.neg) (fun _ => Real.exp_pos _) hs

theorem target_support {m : ℕ} {V : E m → ℝ} (hV : Continuous V) :
    (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))).support = univ :=
  support_withDensity_eq_univ (Real.continuous_exp.comp hV.neg).measurable
    (fun _ => Real.exp_pos _)

theorem gaussian_density_bounds {m : ℕ} {s : Set (E m)} (hs : IsCompact s) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ x ∈ s,
      a ≤ Submission.Lib.EntropyRemainder.gaussianDensity x ∧
        Submission.Lib.EntropyRemainder.gaussianDensity x ≤ b :=
  density_bounds_on_compact Submission.Lib.EntropyRemainder.gaussianDensity_continuous
    Submission.Lib.EntropyRemainder.gaussianDensity_pos hs

end Submission.Obl.Entropy__smooth_gaussian_transport
