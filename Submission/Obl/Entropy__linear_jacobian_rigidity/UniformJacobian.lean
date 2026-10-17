import Mathlib

/-!
Limits of Jacobians, used to extract the homogeneous terms at the origin in
Section 6, Lemma 6.1 of the supplied paper.
-/

namespace Submission.Obl.Entropy__linear_jacobian_rigidity

open Filter Set
open scoped Topology

/-- A limit of derivatives, uniform on every ball, has a primitive when the
primitives are normalized to vanish at the origin. -/
theorem exists_primitive_of_tendstoUniformlyOn_ball
    {ι E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {l : Filter ι} [NeBot l]
    (f : ι → E → V) (f' : ι → E → E →L[ℝ] V) (g' : E → E →L[ℝ] V)
    (hf : ∀ n x, HasFDerivAt (f n) (f' n x) x)
    (hzero : ∀ n, f n 0 = 0)
    (hlim : ∀ r : ℝ, TendstoUniformlyOn f' g' l (Metric.ball 0 r)) :
    ∃ g : E → V, ∀ x, HasFDerivAt g (g' x) x := by
  have hbase : Cauchy (Filter.map (fun n ↦ f n 0) l) := by
    simpa only [hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : V)) l (𝓝 0)).cauchy_map
  have hpoint : ∀ x : E, ∃ y : V, Tendsto (fun n ↦ f n x) l (𝓝 y) := by
    intro x
    apply cauchy_map_iff_exists_tendsto.mp
    exact (uniformCauchySeqOn_ball_of_fderiv (hlim (‖x‖ + 1)).uniformCauchySeqOn
      (fun n y _ ↦ hf n y) hbase).cauchy_map (by simp)
  choose g hg using hpoint
  refine ⟨g, fun x ↦ ?_⟩
  exact hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball (hlim (‖x‖ + 1))
    (fun n y _ ↦ hf n y) (fun y _ ↦ hg y) (by simp)

end Submission.Obl.Entropy__linear_jacobian_rigidity
