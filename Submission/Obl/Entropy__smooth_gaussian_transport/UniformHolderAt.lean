import Submission.Obl.Entropy__smooth_gaussian_transport.HolderLocalization

open Set Filter Asymptotics
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Hölder control on both variable points in a neighborhood of the base point. -/
def UniformHolderAt {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (α : ℝ) (f : X → Y) (x : X) : Prop :=
  (fun p : X × X => f p.1 - f p.2) =O[nhds (x, x)] (fun p => ‖p.1 - p.2‖ ^ α)

/-- Finite smoothness together with uniform local Hölder control of the top derivative. -/
structure HolderRegularAt {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (n : ℕ) (α : ℝ) (f : X → Y) (x : X) : Prop where
  contDiffAt : ContDiffAt ℝ n f x
  holder : UniformHolderAt α (iteratedFDeriv ℝ n f) x

theorem UniformHolderAt.of_bound {X Y : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {α C : ℝ} {f : X → Y} {x : X} {U : Set X} (hU : U ∈ nhds x)
    (hb : ∀ y ∈ U, ∀ z ∈ U, ‖f y - f z‖ ≤ C * ‖y - z‖ ^ α) : UniformHolderAt α f x := by
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [prod_mem_nhds hU hU] with p hp
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hb p.1 hp.1 p.2 hp.2

theorem UniformHolderAt.exists_ball_bound {X Y : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {α : ℝ} {f : X → Y} {x : X} (hf : UniformHolderAt α f x) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ y ∈ Metric.ball x r, ∀ z ∈ Metric.ball x r,
      ‖f y - f z‖ ≤ C * ‖y - z‖ ^ α := by
  obtain ⟨C, hC, hb⟩ := hf.exists_pos
  have hC := hC.le
  have hb := hb.bound
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hb
  refine ⟨r, C, hr, hC, ?_⟩
  intro y hy z hz
  have hp : (y, z) ∈ Metric.ball (x, x) r := by
    simpa only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] using And.intro hy hz
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using show ‖f y - f z‖ ≤ C * ‖‖y - z‖ ^ α‖ from hsub hp

theorem UniformHolderAt.of_contDiffAt_one {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {x : X} {α : ℝ} (hf : ContDiffAt ℝ 1 f x) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    UniformHolderAt α f x := by
  obtain ⟨L, U, hU, hLip⟩ := hf.exists_lipschitzOnWith
  have hB : (fun p : X × X => f p.1 - f p.2) =O[nhds (x, x)] (fun p => ‖p.1 - p.2‖) := by
    apply Asymptotics.IsBigO.of_bound L
    filter_upwards [prod_mem_nhds hU hU] with p hp
    simpa only [dist_eq_norm, norm_norm] using hLip.dist_le_mul p.1 hp.1 p.2 hp.2
  have hnear : Tendsto (fun p : X × X => ‖p.1 - p.2‖) (nhds (x, x)) (nhdsWithin 0 (Ici 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Filter.Eventually.of_forall (fun p => norm_nonneg _)⟩
    simpa only [Pi.sub_apply, sub_self, norm_zero] using (continuous_fst.sub continuous_snd).norm.tendsto (x, x)
  exact hB.trans ((Asymptotics.IsBigO.id_rpow_of_le_one hα1).comp_tendsto hnear)

end Submission.Obl.Entropy__smooth_gaussian_transport
