import Submission.Obl.Entropy__smooth_gaussian_transport.AffineDensity
import Submission.Obl.Entropy__smooth_gaussian_transport.QuadraticApproximation

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- A positive scalar quadratic tangent, in arbitrary linear coordinates,
satisfies the Monge–Ampère density equation at its center. -/
theorem density_eq_of_affine_quadratic_approximation {m : ℕ} {u f : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ) (hf : Continuous f)
    (hMA : alexandrovMeasure u = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (L : E m ≃L[ℝ] E m) (b p : E m) {a : ℝ} (ha : 0 < a)
    (happrox : ∀ ε : ℝ, 0 < ε → ∀ᶠ h : E m in 𝓝 0,
      |u (L h + b) - inner ℝ p h - u b - a / 2 * ‖h‖ ^ 2| ≤ ε * ‖h‖ ^ 2) :
    |L.toLinearMap.det| ^ 2 * f b = a ^ m := by
  apply le_antisymm
  · have hlim : Tendsto (fun δ : ℝ => (a + δ) ^ m) (𝓝[>] 0) (𝓝 (a ^ m)) := by
      have hc : Continuous (fun δ : ℝ => (a + δ) ^ m) := by fun_prop
      simpa only [add_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδpos : 0 < δ := hδ
    apply density_le_of_affine_upper_quadratic_touch hu hdom hf hMA L b p
      (add_pos ha hδpos)
    filter_upwards [happrox (δ / 2) (half_pos hδpos)] with h hh
    have hh' := (abs_le.mp hh).2
    nlinarith
  · have hlim : Tendsto (fun δ : ℝ => (a - δ) ^ m) (𝓝[>] 0) (𝓝 (a ^ m)) := by
      have hc : Continuous (fun δ : ℝ => (a - δ) ^ m) := by fun_prop
      simpa only [sub_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    apply le_of_tendsto hlim
    have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < a :=
      (gt_mem_nhds ha).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with δ hδ hδa
    have hδpos : 0 < δ := hδ
    apply density_ge_of_affine_lower_quadratic_touch hu hdom hf hMA L b p (sub_pos.mpr hδa)
    filter_upwards [happrox (δ / 2) (half_pos hδpos)] with h hh
    have hh' := (abs_le.mp hh).1
    nlinarith

end Submission.Obl.Entropy__smooth_gaussian_transport
