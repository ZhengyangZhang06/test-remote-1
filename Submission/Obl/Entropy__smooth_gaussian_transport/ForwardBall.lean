import Submission.Obl.Entropy__smooth_gaussian_transport.AlmostEverywhereHessian

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Monotonicity prevents a large value of a map from disappearing on the
ball of radius one half a unit step forward. -/
theorem norm_le_three_mul_norm_on_forward_ball {m : ℕ} {T : E m → E m}
    (hT : ∀ x y, 0 ≤ inner ℝ (T x - T y) (x - y))
    {x : E m} (hx : T x ≠ 0) {z : E m}
    (hz : z ∈ Metric.ball (x + ‖T x‖⁻¹ • T x) (1 / 2 : ℝ)) :
    ‖T x‖ ≤ 3 * ‖T z‖ := by
  let e := ‖T x‖⁻¹ • T x
  have hp : 0 < ‖T x‖ := norm_pos_iff.mpr hx
  have he : ‖e‖ = 1 := by
    simp only [e, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ hp.ne'
  have hie : inner ℝ (T x) e = ‖T x‖ := by
    simp only [e, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hdist : ‖z - (x + e)‖ < 1 / 2 := hz
  have hnorm : ‖z - x‖ < 3 / 2 := by
    have hh := norm_add_le (z - (x + e)) e
    have hh' : z - (x + e) + e = z - x := by abel
    rw [hh', he] at hh
    linarith
  have hl := (abs_le.mp (abs_real_inner_le_norm (T x) (z - (x + e)))).1
  have hs : z - x = e + (z - (x + e)) := by abel
  have hlo : ‖T x‖ / 2 ≤ inner ℝ (T x) (z - x) := by
    rw [hs, inner_add_right, hie]
    nlinarith [mul_lt_mul_of_pos_left hdist hp]
  have hmono := hT z x
  rw [inner_sub_left] at hmono
  have hup := real_inner_le_norm (T z) (z - x)
  have hnormmul := mul_le_mul_of_nonneg_left hnorm.le (norm_nonneg (T z))
  linarith

theorem norm_lt_norm_add_two_on_forward_ball {m : ℕ} {p x z : E m} (hp : p ≠ 0)
    (hz : z ∈ Metric.ball (x + ‖p‖⁻¹ • p) (1 / 2 : ℝ)) : ‖z‖ < ‖x‖ + 2 := by
  have he : ‖‖p‖⁻¹ • p‖ = 1 := by
    simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp)
  have hdist : ‖z - (x + ‖p‖⁻¹ • p)‖ < 1 / 2 := hz
  have h₁ := norm_add_le (z - (x + ‖p‖⁻¹ • p)) (x + ‖p‖⁻¹ • p)
  rw [sub_add_cancel] at h₁
  have h₂ := norm_add_le x (‖p‖⁻¹ • p)
  rw [he] at h₂
  linarith

end Submission.Obl.Entropy__smooth_gaussian_transport
