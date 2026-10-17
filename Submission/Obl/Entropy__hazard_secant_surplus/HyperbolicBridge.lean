import Submission.Obl.Entropy__hazard_secant_surplus.LogCoordinates

open MeasureTheory Set

namespace Submission.Obl.Entropy__hazard_secant_surplus

lemma sinh_log_separation (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    4 * u * v * Real.sinh ((Real.log v - Real.log u) / 2) ^ 2 = (v - u) ^ 2 := by
  have hd : 2 * ((Real.log v - Real.log u) / 2) = Real.log v - Real.log u := by ring
  have hc := Real.cosh_two_mul ((Real.log v - Real.log u) / 2)
  rw [hd, Real.cosh_eq, Real.exp_sub, Real.exp_log hv, Real.exp_log hu,
    show -(Real.log v - Real.log u) = Real.log u - Real.log v by ring,
    Real.exp_sub, Real.exp_log hu, Real.exp_log hv] at hc
  have hs := Real.cosh_sq_sub_sinh_sq ((Real.log v - Real.log u) / 2)
  have hh : (v / u + u / v) / 2 = 1 + 2 * Real.sinh ((Real.log v - Real.log u) / 2) ^ 2 := by
    linarith
  field_simp [ne_of_gt hu, ne_of_gt hv] at hh
  nlinarith

lemma log_secant_scale {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hδ : Real.log v - Real.log u ≠ 0) :
    ((v - u) / (Real.log v - Real.log u)) ^ 2 / (u * v) =
      (Real.sinh ((Real.log v - Real.log u) / 2) / ((Real.log v - Real.log u) / 2)) ^ 2 := by
  have h := sinh_log_separation u v hu hv
  field_simp [hδ, ne_of_gt hu, ne_of_gt hv]
  nlinarith

lemma integral_shift_midpoint (f : ℝ → ℝ) (u v : ℝ) :
    (∫ s in -((v - u) / 2)..(v - u) / 2, f ((u + v) / 2 + s)) = ∫ s in u..v, f s := by
  have hl : (u + v) / 2 + -((v - u) / 2) = u := by ring
  have hr : (u + v) / 2 + (v - u) / 2 = v := by ring
  simpa only [hl, hr] using
    (intervalIntegral.integral_comp_add_left (a := -((v - u) / 2)) (b := (v - u) / 2)
      f ((u + v) / 2))

end Submission.Obl.Entropy__hazard_secant_surplus
