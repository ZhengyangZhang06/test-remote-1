import Submission.Obl.Entropy__continuous_jacobian_of_l2_limit.Mollifier

open MeasureTheory Set Filter Metric ContinuousLinearMap
open scoped Topology Convolution Pointwise

namespace Submission.Obl.Entropy__continuous_jacobian_of_l2_limit

variable {m : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [CompleteSpace Y]
local notation "E" => EuclideanSpace ℝ (Fin m)

/-- Convolution with a fixed smooth bump turns local L1 convergence into locally uniform
convergence, in any Banach codomain. -/
lemma mollify_tendsto_of_localL1 (φ : ContDiffBump (0 : E))
    {u : ℕ → E → Y} {f : E → Y}
    (hu : ∀ n, LocallyIntegrable (u n) volume) (hf : LocallyIntegrable f volume)
    (hlim : ∀ K : Set E, IsCompact K →
      Tendsto (fun n => ∫ x in K, ‖u n x - f x‖) atTop (𝓝 0)) :
    TendstoLocallyUniformly (fun n => mollify φ (u n)) (mollify φ f) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  let S := -tsupport (φ.normed volume) + K
  have hS : IsCompact S := φ.hasCompactSupport_normed.isCompact.neg.add hK
  let L : ℝ →L[ℝ] Y →L[ℝ] Y := lsmul ℝ ℝ
  let C := ‖L‖ * ⨆ t : E, ‖φ.normed volume t‖
  have ht : Tendsto (fun n => C * ∫ x in S, ‖u n x - f x‖) atTop (𝓝 0) := by
    simpa using (hlim S hS).const_mul C
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [ht.eventually_lt_const hε] with n hn x hx
  apply lt_of_le_of_lt _ hn
  have hiu := ((φ.hasCompactSupport_normed (μ := volume)).convolutionExists_left L
    φ.continuous_normed (hu n) x).integrable_swap
  have hif := ((φ.hasCompactSupport_normed (μ := volume)).convolutionExists_left L
    φ.continuous_normed hf x).integrable_swap
  rw [dist_eq_norm']
  simp only [mollify, convolution_eq_swap]
  rw [← integral_sub hiu hif]
  calc
    ‖∫ t, (lsmul ℝ ℝ) (φ.normed volume (x-t)) (u n t) -
        (lsmul ℝ ℝ) (φ.normed volume (x-t)) (f t)‖ ≤
        ∫ t, S.indicator (fun t => C * ‖u n t - f t‖) t := by
      apply norm_integral_le_of_norm_le
      · rw [integrable_indicator_iff hS.measurableSet]
        exact (((hu n).sub hf).integrableOn_isCompact hS).norm.const_mul C
      · apply ae_of_all
        intro t
        simpa only [map_sub] using
          ((φ.hasCompactSupport_normed (μ := volume)).convolution_integrand_bound_left
            (g := fun t => u n t - f t) L φ.continuous_normed hx (t := t))
    _ = C * ∫ t in S, ‖u n t - f t‖ := by
      rw [integral_indicator hS.measurableSet, integral_const_mul]

/-- Local L1 convergence of a C1 sequence and its derivatives identifies the derivative
of every mollification of its limit. -/
lemma mollify_limit_hasFDerivAt (φ : ContDiffBump (0 : E))
    {u : ℕ → E → Y} {f : E → Y} {j : E → E →L[ℝ] Y}
    (hu : ∀ n, ContDiff ℝ 1 (u n))
    (hf : LocallyIntegrable f volume) (hj : Continuous j)
    (hlim : ∀ K : Set E, IsCompact K →
      Tendsto (fun n => ∫ x in K, ‖u n x - f x‖) atTop (𝓝 0))
    (hdlim : ∀ K : Set E, IsCompact K →
      Tendsto (fun n => ∫ x in K, ‖fderiv ℝ (u n) x - j x‖) atTop (𝓝 0))
    (x : E) : HasFDerivAt (mollify φ f) (mollify φ j x) x := by
  have hv := mollify_tendsto_of_localL1 φ (fun n => (hu n).continuous.locallyIntegrable)
    hf hlim
  have hd := mollify_tendsto_of_localL1 φ
    (fun n => ((hu n).continuous_fderiv one_ne_zero).locallyIntegrable)
    hj.locallyIntegrable hdlim
  exact hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ
    hd.tendstoLocallyUniformlyOn (fun n y _ => mollify_hasFDerivAt φ (hu n) y)
    (fun y _ => hv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ y)) (mem_univ x)

end Submission.Obl.Entropy__continuous_jacobian_of_l2_limit
