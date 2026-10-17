import Submission.Obl.Entropy__smooth_gaussian_transport.ContactMeasure
import Submission.Obl.Entropy__smooth_gaussian_transport.DeterminantConcavity

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- At a supporting contact point, an existing Hessian is nonnegative. Only
pointwise differentiability of the gradient is used. -/
theorem nonneg_hessian_of_local_support {m : ℕ} {u : E m → ℝ}
    (hu : Differentiable ℝ u) {x : E m} {A : E m →L[ℝ] E m}
    (hA : HasFDerivAt (gradient u) A x)
    (hs : ∀ᶠ y in 𝓝 x, u x + inner ℝ (gradient u x) (y - x) ≤ u y)
    (v : E m) : 0 ≤ inner ℝ (A v) v := by
  by_cases hv : v = 0
  · simp only [hv, map_zero, inner_zero_left, le_refl]
  by_contra hn
  have hq : inner ℝ (A v) v < 0 := lt_of_not_ge hn
  let ε := -inner ℝ (A v) v / (4 * ‖v‖ ^ 2)
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hε : 0 < ε := div_pos (neg_pos.mpr hq) (by positivity)
  have hεeq : ε * ‖v‖ ^ 2 = -inner ℝ (A v) v / 4 := by
    dsimp [ε]
    field_simp
  have herr := (quadratic_expansion_of_hasFDerivAt_gradient hu hA).bound hε
  have hshift : Tendsto (fun h : E m => x + h) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun h : E m => x + h) := continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto (0 : E m)
  have hs0 := hshift.eventually hs
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (herr.and hs0)
  let t := r / (2 * (‖v‖ + 1))
  have ht : 0 < t := div_pos hr (by positivity)
  have htr : t * (2 * (‖v‖ + 1)) = r := div_mul_cancel₀ _ (by positivity)
  have htv : ‖t • v‖ < r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith
  obtain ⟨he, hh⟩ := hball (by simpa only [Metric.mem_ball, dist_zero_right] using htv)
  simp only [Real.norm_eq_abs, norm_smul, abs_of_pos ht, mul_pow] at he
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg t) (sq_nonneg ‖v‖))] at he
  simp only [add_sub_cancel_left] at hh
  have he' := (abs_le.mp he).2
  simp only [quadraticError, map_smul, real_inner_smul_left, real_inner_smul_right] at he'
  have hc : ε * (t ^ 2 * ‖v‖ ^ 2) = (-inner ℝ (A v) v / 4) * t ^ 2 := by
    calc
      _ = (ε * ‖v‖ ^ 2) * t ^ 2 := by ring
      _ = _ := by rw [hεeq]
  rw [hc] at he'
  have hneg : inner ℝ (A v) v * t ^ 2 < 0 := mul_neg_of_neg_of_pos hq (sq_pos_of_pos ht)
  rw [real_inner_smul_right] at hh
  nlinarith

theorem contact_hessian_posSemidef {m : ℕ} {u : E m → ℝ} (hu : ContDiff ℝ 1 u)
    {K : Set (E m)} {x : E m} (hx : x ∈ lowerContactSet u K)
    (hd : DifferentiableAt ℝ (gradient u) x) :
    (operatorMatrix (fderiv ℝ (gradient u) x)).PosSemidef := by
  apply operatorMatrix_posSemidef (symmetric_gradient_derivative hu.differentiable_one hd.hasFDerivAt)
  apply nonneg_hessian_of_local_support hu.differentiable_one hd.hasFDerivAt
  filter_upwards [mem_interior_iff_mem_nhds.mp hx.1] with y hy
  exact hx.2.2 y hy

end Submission.Obl.Entropy__smooth_gaussian_transport
