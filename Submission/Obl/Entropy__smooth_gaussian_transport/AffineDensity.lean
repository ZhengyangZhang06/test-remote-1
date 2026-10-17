import Submission.Obl.Entropy__smooth_gaussian_transport.AffineChange
import Submission.Obl.Entropy__smooth_gaussian_transport.QuadraticTests
import Submission.Obl.Entropy__smooth_gaussian_transport.DepthEstimate
import Submission.Obl.Entropy__smooth_gaussian_transport.DifferentiableTransport

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Under a change of variables, the Alexandrov density gains the square of
the absolute determinant. Subtracting an affine function does not change it. -/
theorem affineChange_alexandrov_density {m : ℕ} {u f : E m → ℝ}
    (hu : Continuous u) (hdom : conjugateDomain u = univ)
    (hMA : alexandrovMeasure u = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (L : E m ≃L[ℝ] E m) (b p : E m) (r : ℝ) :
    alexandrovMeasure (fun x => u (L x + b) - inner ℝ p x - r) =
      volume.withDensity (fun x => ENNReal.ofReal (|L.toLinearMap.det| ^ 2 * f (L x + b))) := by
  ext s hs
  have hs' : MeasurableSet ((fun x => L x + b) '' s) :=
    (L.toHomeomorph.trans (Homeomorph.addRight b)).measurableEmbedding.measurableSet_image.mpr hs
  have ha : alexandrovMeasure (fun x => u (L x + b) - inner ℝ p x - r) s =
      ENNReal.ofReal |L.toLinearMap.det| * alexandrovMeasure u ((fun x => L x + b) '' s) := by
    simpa only [one_pow, one_mul] using
      affineChange_alexandrov hu hdom L b p r (a := 1) zero_lt_one hs
  rw [ha, hMA, withDensity_apply _ hs', withDensity_apply _ hs]
  have hd (x : E m) (_ : x ∈ s) :
      HasFDerivWithinAt (fun x => L x + b) L.toContinuousLinearMap s x :=
    (L.toContinuousLinearMap.hasFDerivAt.add_const b).hasFDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hd
    (L.toHomeomorph.trans (Homeomorph.addRight b)).injective.injOn]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (abs_nonneg _)]
  change ENNReal.ofReal |L.toLinearMap.det| *
      (ENNReal.ofReal |L.toLinearMap.det| * ENNReal.ofReal (f (L x + b))) = _
  ring

theorem affine_centered_convex {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (L : E m ≃L[ℝ] E m) (b p : E m) :
    ConvexOn ℝ univ (fun x => u (L x + b) - inner ℝ p x - u b) := by
  have hc : ConvexOn ℝ univ ((fun z => u (z + b)) ∘ L) := by
    convert! (translate_convex hu b).comp_linearMap L.toLinearMap using 1
  exact tilt_convex hc p (u b)

theorem affine_centered_conjugateDomain {m : ℕ} {u : E m → ℝ}
    (hdom : conjugateDomain u = univ) (L : E m ≃L[ℝ] E m) (b p : E m) :
    conjugateDomain (fun x => u (L x + b) - inner ℝ p x - u b) = univ :=
  tilt_conjugateDomain (linearChange_conjugateDomain (translate_conjugateDomain hdom b) L) p (u b)

/-- The quadratic upper-test inequality is invariant under arbitrary invertible
linear coordinates and translation of the contact point. -/
theorem density_le_of_affine_upper_quadratic_touch {m : ℕ} {u f : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ) (hf : Continuous f)
    (hMA : alexandrovMeasure u = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (L : E m ≃L[ℝ] E m) (b p : E m) {a : ℝ} (ha : 0 < a)
    (htouch : ∀ᶠ x in 𝓝 (0 : E m),
      u (L x + b) - inner ℝ p x - u b ≤ a / 2 * ‖x‖ ^ 2) :
    |L.toLinearMap.det| ^ 2 * f b ≤ a ^ m := by
  have hc : Continuous (fun x => |L.toLinearMap.det| ^ 2 * f (L x + b)) :=
    continuous_const.mul (hf.comp (L.continuous.add continuous_const))
  have ht := density_le_of_upper_quadratic_touch (affine_centered_convex hu L b p)
    (affine_centered_conjugateDomain hdom L b p) hc
    (affineChange_alexandrov_density hu.locallyLipschitz.continuous hdom hMA L b p (u b))
    (by simp) ha htouch
  simpa only [map_zero, zero_add] using ht

theorem density_ge_of_affine_lower_quadratic_touch {m : ℕ} {u f : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ) (hf : Continuous f)
    (hMA : alexandrovMeasure u = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (L : E m ≃L[ℝ] E m) (b p : E m) {a : ℝ} (ha : 0 < a)
    (htouch : ∀ᶠ x in 𝓝 (0 : E m),
      a / 2 * ‖x‖ ^ 2 ≤ u (L x + b) - inner ℝ p x - u b) :
    a ^ m ≤ |L.toLinearMap.det| ^ 2 * f b := by
  have hc : Continuous (fun x => |L.toLinearMap.det| ^ 2 * f (L x + b)) :=
    continuous_const.mul (hf.comp (L.continuous.add continuous_const))
  have ht := density_ge_of_lower_quadratic_touch (affine_centered_convex hu L b p)
    (affine_centered_conjugateDomain hdom L b p) hc
    (affineChange_alexandrov_density hu.locallyLipschitz.continuous hdom hMA L b p (u b))
    (by simp) ha htouch
  simpa only [map_zero, zero_add] using ht

/-- The Gaussian transport potential satisfies both quadratic contact
inequalities for its Monge–Ampère equation, in arbitrary affine coordinates. -/
theorem brenier_affine_quadratic_tests {m : ℕ} (hm : 1 ≤ m) {V φ : E m → ℝ}
    (hV : Continuous V) (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (ProbabilityTheory.stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    (L : E m ≃L[ℝ] E m) (b p : E m) {a : ℝ} (ha : 0 < a) :
    ((∀ᶠ x in 𝓝 (0 : E m), φ (L x + b) - inner ℝ p x - φ b ≤ a / 2 * ‖x‖ ^ 2) →
      |L.toLinearMap.det| ^ 2 *
        (Submission.Lib.EntropyRemainder.gaussianDensity b * Real.exp (V (gradient φ b))) ≤ a ^ m) ∧
    ((∀ᶠ x in 𝓝 (0 : E m), a / 2 * ‖x‖ ^ 2 ≤ φ (L x + b) - inner ℝ p x - φ b) →
      a ^ m ≤ |L.toLinearMap.det| ^ 2 *
        (Submission.Lib.EntropyRemainder.gaussianDensity b * Real.exp (V (gradient φ b)))) := by
  have hdom : conjugateDomain φ = univ := by
    apply conjugateDomain_eq_univ_of_transport hφ (stdGaussian_absolutelyContinuous m)
    rw [hlaw]
    exact target_support hV
  have hf := brenier_alexandrov_continuous_density hm hV hφ hlaw
  have hMA := brenier_alexandrov_density hV hφ hlaw
  exact ⟨density_le_of_affine_upper_quadratic_touch hφ hdom hf hMA L b p ha,
    density_ge_of_affine_lower_quadratic_touch hφ hdom hf hMA L b p ha⟩

end Submission.Obl.Entropy__smooth_gaussian_transport
