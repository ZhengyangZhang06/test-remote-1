import Submission.Obl.Entropy__smooth_gaussian_transport.GlobalSecondDifference
import Submission.Obl.Entropy__smooth_gaussian_transport.QuadraticApproximation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem quadratic_error_bound_of_second_difference {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hd : Differentiable ℝ u) {C : ℝ}
    (hsecond : ∀ h x, symmetricAverage u h x - u x ≤ C * ‖h‖ ^ 2) (x h : E m) :
    |quadraticError u x (gradient u x) 0 h| ≤ 2 * C * ‖h‖ ^ 2 := by
  have hp := convex_gradient_support hu (hd x) (x + h)
  have hn := convex_gradient_support hu (hd x) (x - h)
  simp only [add_sub_cancel_left] at hp
  have he : x - h - x = -h := by abel
  rw [he, inner_neg_right] at hn
  have hs := hsecond h x
  simp only [symmetricAverage] at hs
  have hnonneg : 0 ≤ u (x + h) - u x - inner ℝ (gradient u x) h := by linarith
  simp only [quadraticError, zero_apply, inner_zero_left, mul_zero,
    sub_zero, abs_of_nonneg hnonneg]
  linarith

/-- A global quadratic bound on centered differences gives a global
Lipschitz bound on the gradient, with an explicit nonoptimal constant. -/
theorem gradient_lipschitz_of_second_difference {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hd : Differentiable ℝ u) {C : ℝ} (hC : 0 ≤ C)
    (hsecond : ∀ h x, symmetricAverage u h x - u x ≤ C * ‖h‖ ^ 2) :
    LipschitzWith ⟨10 * C, by positivity⟩ (gradient u) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  change ‖gradient u x - gradient u y‖ ≤ 10 * C * ‖x - y‖
  by_cases hxy : x = y
  · simp [hxy]
  have hr : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hz : (0 : E m →ₗ[ℝ] E m).IsSymmetric := by
    intro v w
    simp
  have hsupport : IsSubgradient u (y + (x - y)) (gradient u x) := by
    rw [add_sub_cancel]
    exact convex_gradient_support hu (hd x)
  have hb := subgradient_bound_of_quadratic_error (A := (0 : E m →L[ℝ] E m))
    (x := y) (p := gradient u y) (h := x - y) (q := gradient u x) hz
    (show 0 ≤ 2 * C by positivity) hr (ρ := 2 * ‖x - y‖ + 1) (by linarith)
    (fun z _ => quadratic_error_bound_of_second_difference hu hd hsecond y z) hsupport
  simp only [zero_apply, sub_zero, norm_zero, zero_div, zero_mul, zero_add] at hb
  apply (mul_le_mul_iff_right₀ hr).mp
  nlinarith only [hb]

theorem brenier_gradient_lipschitz {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    LipschitzWith ⟨10 * (1 / Real.sqrt a), by positivity⟩ (gradient φ) := by
  apply gradient_lipschitz_of_second_difference hφ
    (brenier_contDiff_one hm hV.continuous hφ hlaw).1.differentiable_one (by positivity)
  intro h x
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using
    brenier_global_second_difference hm hV ha hH hφ hlaw h x

end Submission.Obl.Entropy__smooth_gaussian_transport
