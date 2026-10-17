import Submission.Obl.Entropy__smooth_gaussian_transport.AeMeanValue

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem exists_mem_ball_of_ae {m : ℕ} {P : E m → Prop} (hP : ∀ᵐ x ∂volume, P x)
    (c : E m) {r : ℝ} (hr : 0 < r) : ∃ x ∈ Metric.ball c r, P x := by
  by_contra hn
  push Not at hn
  have hsub : Metric.ball c r ⊆ {x | ¬ P x} := fun x hx => hn x hx
  have hz : volume (Metric.ball c r) = 0 := measure_mono_null hsub (ae_iff.mp hP)
  exact (Metric.measure_ball_pos volume c hr).ne' hz

/-- An operator field with vanishing essential oscillation on balls has an
essential limit at their center. The radius sequence need not be monotone. -/
theorem exists_essential_limit_of_oscillation {m : ℕ}
    (H : E m → E m →L[ℝ] E m) (c : E m) (ρ ε : ℕ → ℝ)
    (hρ : ∀ n, 0 < ρ n) (hε : ∀ n, 0 ≤ ε n)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hosc : ∀ n, ∀ᵐ x ∂volume, ∀ᵐ y ∂volume,
      x ∈ Metric.ball c (ρ n) → y ∈ Metric.ball c (ρ n) → ‖H y - H x‖ ≤ ε n) :
    ∃ A : E m →L[ℝ] E m, ∀ n, ∀ᵐ y ∂volume,
      y ∈ Metric.ball c (ρ n) → ‖H y - A‖ ≤ 2 * ε n := by
  have hex (n : ℕ) : ∃ x : E m, ∀ᵐ y ∂volume,
      y ∈ Metric.ball c (ρ n) → ‖H y - H x‖ ≤ ε n := by
    obtain ⟨x, hx, hxy⟩ := exists_mem_ball_of_ae (hosc n) c (hρ n)
    exact ⟨x, hxy.mono (fun y hy => hy hx)⟩
  choose x hx using hex
  let a : ℕ → E m →L[ℝ] E m := fun n => H (x n)
  have hpair (n j : ℕ) : ‖a n - a j‖ ≤ ε n + ε j := by
    obtain ⟨y, hy, hyn, hyj⟩ := exists_mem_ball_of_ae ((hx n).and (hx j)) c
      (lt_min (hρ n) (hρ j))
    have hn : y ∈ Metric.ball c (ρ n) := (Metric.mem_ball.mp hy).trans_le (min_le_left _ _)
    have hj : y ∈ Metric.ball c (ρ j) := (Metric.mem_ball.mp hy).trans_le (min_le_right _ _)
    calc
      ‖a n - a j‖ ≤ ‖a n - H y‖ + ‖H y - a j‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖H y - a n‖ + ‖H y - a j‖ := by rw [norm_sub_rev (a n) (H y)]
      _ ≤ ε n + ε j := add_le_add (hyn hn) (hyj hj)
  have hcauchy : CauchySeq a := by
    apply Metric.cauchySeq_iff.mpr
    intro d hd
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hεlim.eventually (gt_mem_nhds (by positivity : 0 < d / 3)))
    refine ⟨N, ?_⟩
    intro n hn j hj
    rw [dist_eq_norm]
    have hh := hpair n j
    linarith [hN n hn, hN j hj]
  obtain ⟨A, hA⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hclose (n : ℕ) : ‖a n - A‖ ≤ ε n := by
    have hl : Tendsto (fun j => ‖a n - a j‖) atTop (𝓝 ‖a n - A‖) :=
      (tendsto_const_nhds.sub hA).norm
    have hr : Tendsto (fun j => ε n + ε j) atTop (𝓝 (ε n)) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := ε n)).add hεlim
    exact le_of_tendsto_of_tendsto' hl hr (hpair n)
  refine ⟨A, fun n => ?_⟩
  filter_upwards [hx n] with y hy
  intro hyb
  calc
    ‖H y - A‖ ≤ ‖H y - a n‖ + ‖a n - A‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε n + ε n := add_le_add (hy hyb) (hclose n)
    _ = _ := by ring

/-- A Lipschitz function differentiates at a point when its derivative has an
essential limit there. This uses the everywhere mean-value remainder bound. -/
theorem hasFDerivAt_of_essential_derivative_limit {m : ℕ} {f : E m → E m} {L : NNReal}
    (hf : LipschitzWith L f) {c : E m} {A : E m →L[ℝ] E m}
    (hlimit : ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∀ᵐ y ∂volume,
      y ∈ Metric.ball c r → ‖fderiv ℝ f y - A‖ ≤ ε) : HasFDerivAt f A c := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  obtain ⟨r, hr, hb⟩ := hlimit ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : E m) hr] with h hh
  have hc : c ∈ Metric.ball c r := Metric.mem_ball_self hr
  have hch : c + h ∈ Metric.ball c r := by
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hh
  have hbound := linear_remainder_of_ae_fderiv_bound hf Metric.isOpen_ball (convex_ball _ _)
    A hε.le hb hc hch
  simpa only [add_sub_cancel_left] using hbound

end Submission.Obl.Entropy__smooth_gaussian_transport
