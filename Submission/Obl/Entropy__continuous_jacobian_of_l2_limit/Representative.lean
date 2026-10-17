import Mathlib

open MeasureTheory Set Filter Metric
open scoped Topology

namespace Submission.Obl.Entropy__continuous_jacobian_of_l2_limit

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- A locally uniform derivative limit and an almost-everywhere function limit determine
one global continuously differentiable representative. -/
theorem representative_of_locally_uniform_derivatives {μ : Measure E} [NeZero μ]
    {u : ℕ → E → Y} {du : ℕ → E → E →L[ℝ] Y} {f : E → Y}
    {j : E → E →L[ℝ] Y}
    (hu : ∀ n x, HasFDerivAt (u n) (du n x) x)
    (hj : Continuous j)
    (hdu : TendstoLocallyUniformly du j atTop)
    (hf : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (f x))) :
    ∃ g : E → Y, ContDiff ℝ 1 g ∧ g =ᵐ[μ] f ∧ ∀ x, fderiv ℝ g x = j x := by
  obtain ⟨x₀, hx₀⟩ := hf.exists
  have hC : ∀ x : E, CauchySeq (fun n => u n x) := by
    intro x
    let r := dist x x₀ + 1
    have hr : 0 < r := by dsimp [r]; positivity
    have hd : TendstoUniformlyOn du j atTop (closedBall x₀ r) :=
      tendstoLocallyUniformly_iff_forall_isCompact.mp hdu _ (isCompact_closedBall _ _)
    have hc := uniformCauchySeqOn_ball_of_fderiv
      (hd.mono ball_subset_closedBall).uniformCauchySeqOn
      (fun n y _ => hu n y) hx₀.cauchy_map
    exact hc.cauchy_map (by dsimp [r]; simp only [mem_ball]; linarith)
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hC x)
  have hg' : ∀ x, HasFDerivAt g (j x) x := by
    intro x
    exact hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ
      hdu.tendstoLocallyUniformlyOn (fun n y _ => hu n y) (fun y _ => hg y) (mem_univ x)
  refine ⟨g, contDiff_one_iff_hasFDerivAt.mpr ⟨j, hj, hg'⟩, ?_, fun x => (hg' x).fderiv⟩
  filter_upwards [hf] with x hx
  exact tendsto_nhds_unique (hg x) hx

end Submission.Obl.Entropy__continuous_jacobian_of_l2_limit
