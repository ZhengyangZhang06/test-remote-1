import Submission.Obl.Entropy__smooth_gaussian_transport.HolderInterpolation
import Submission.Obl.Entropy__smooth_gaussian_transport.SmallHolderScale

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem uniformCauchy_derivatives_of_holder
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : ℕ → X → Y} {C α : ℝ}
    (hf : ∀ n, Differentiable ℝ (f n)) (hC : 0 ≤ C) (hα : 0 < α)
    (hc : UniformCauchySeqOn f atTop univ)
    (hmod : ∀ n x y, ‖fderiv ℝ (f n) x - fderiv ℝ (f n) y‖ ≤ C * ‖x - y‖ ^ α) :
    UniformCauchySeqOn (fun n => fderiv ℝ (f n)) atTop univ := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨t, ht, hsmall⟩ := exists_small_holder_scale hα (half_pos hε) (2 * C)
  obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hc (ε * t / 8) (by positivity)
  refine ⟨N, ?_⟩
  intro n hn k hk x _
  have hd (z : X) : fderiv ℝ (fun y => f n y - f k y) z =
      fderiv ℝ (f n) z - fderiv ℝ (f k) z :=
    ((hf n z).hasFDerivAt.sub (hf k z).hasFDerivAt).fderiv
  have hb (z : X) : ‖f n z - f k z‖ ≤ ε * t / 8 := by
    simpa only [dist_eq_norm] using (hN n hn k hk z (mem_univ z)).le
  have hdm (z w : X) :
      ‖fderiv ℝ (fun y => f n y - f k y) z - fderiv ℝ (fun y => f n y - f k y) w‖ ≤
        (2 * C) * ‖z - w‖ ^ α := by
    rw [hd, hd]
    have he : (fderiv ℝ (f n) z - fderiv ℝ (f k) z) -
        (fderiv ℝ (f n) w - fderiv ℝ (f k) w) =
        (fderiv ℝ (f n) z - fderiv ℝ (f n) w) -
          (fderiv ℝ (f k) z - fderiv ℝ (f k) w) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans ((add_le_add (hmod n z w) (hmod k z w)).trans_eq (by ring))
  have hh := derivative_holder_interpolation ((hf n).sub (hf k)) (by positivity)
    (show 0 ≤ 2 * C by positivity) hα.le ht hb hdm x
  change ‖fderiv ℝ (fun y => f n y - f k y) x‖ ≤ _ at hh
  rw [hd] at hh
  rw [dist_eq_norm]
  apply lt_of_le_of_lt hh
  have he : 2 * (ε * t / 8) / t = ε / 4 := by field_simp; ring
  rw [he]
  linarith

/-- Uniform convergence and a common Hölder bound on the derivatives imply
uniform convergence of the derivatives and differentiability of the limit. -/
theorem contDiff_one_of_uniform_limit_holder_derivative
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {f : ℕ → X → Y} {g : X → Y} {C α : ℝ}
    (hf : ∀ n, ContDiff ℝ 1 (f n)) (hC : 0 ≤ C) (hα : 0 < α)
    (hfg : TendstoUniformly f g atTop)
    (hmod : ∀ n x y, ‖fderiv ℝ (f n) x - fderiv ℝ (f n) y‖ ≤ C * ‖x - y‖ ^ α) :
    ContDiff ℝ 1 g ∧ TendstoUniformly (fun n => fderiv ℝ (f n)) (fderiv ℝ g) atTop ∧
      ∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ C * ‖x - y‖ ^ α := by
  have hcu := uniformCauchy_derivatives_of_holder (fun n => (hf n).differentiable_one) hC hα
    ((tendstoUniformlyOn_univ.mpr hfg).uniformCauchySeqOn) hmod
  have hc (x : X) : CauchySeq (fun n => fderiv ℝ (f n) x) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hcu ε hε
    exact ⟨N, fun n hn k hk => hN n hn k hk x (mem_univ x)⟩
  choose D hD using fun x => cauchySeq_tendsto_of_complete (hc x)
  have hUD : TendstoUniformly (fun n => fderiv ℝ (f n)) D atTop :=
    tendstoUniformlyOn_univ.mp (hcu.tendstoUniformlyOn_of_tendsto (fun x _ => hD x))
  have hder (x : X) : HasFDerivAt g (D x) x :=
    hasFDerivAt_of_tendstoUniformly hUD
      (fun n x => ((hf n).differentiable_one x).hasFDerivAt) hfg.tendsto_at x
  have hcont : Continuous D := hUD.continuous
    (Frequently.of_forall (fun n => (hf n).continuous_fderiv (by norm_num)))
  have he : D = fderiv ℝ g := funext (fun x => (hder x).fderiv.symm)
  refine ⟨contDiff_one_iff_hasFDerivAt.mpr ⟨D, hcont, hder⟩, he ▸ hUD, ?_⟩
  intro x y
  rw [← he]
  exact le_of_tendsto ((hD x).sub (hD y)).norm (Eventually.of_forall (fun n => hmod n x y))

end Submission.Obl.Entropy__smooth_gaussian_transport
