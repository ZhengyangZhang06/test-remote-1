import Mathlib

open Set
open scoped Topology

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- A bounded function with Hölder derivative has a derivative bounded by
an arbitrarily small multiple of its Hölder constant, at the cost of a
larger multiple of its size. -/
theorem derivative_holder_interpolation {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {M C α t : ℝ} (hf : Differentiable ℝ f)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hα : 0 ≤ α) (ht : 0 < t)
    (hb : ∀ x, ‖f x‖ ≤ M)
    (hmod : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ C * ‖x - y‖ ^ α)
    (x : X) : ‖fderiv ℝ f x‖ ≤ 2 * M / t + C * t ^ α := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  let g : X → Y := fun y => f y - fderiv ℝ f x (y - x)
  have hd (y : X) : HasFDerivAt g (fderiv ℝ f y - fderiv ℝ f x) y := by
    convert! (hf y).hasFDerivAt.sub ((fderiv ℝ f x).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x)) using 1
  have hbound (y : X) (hy : y ∈ Metric.closedBall x t) :
      ‖fderiv ℝ g y‖ ≤ C * t ^ α := by
    rw [(hd y).fderiv]
    exact (hmod y x).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy) hα) hC)
  have hdiff : ‖(x + t • v) - x‖ = t := by
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hv, mul_one]
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y (_ : y ∈ Metric.closedBall x t) => (hd y).differentiableAt) hbound
    (convex_closedBall x t) (x := x) (y := x + t • v)
    (Metric.mem_closedBall_self ht.le) (by simp only [Metric.mem_closedBall, dist_eq_norm, hdiff, le_refl])
  rw [hdiff] at hh
  have hrem : ‖f (x + t • v) - f x - t • fderiv ℝ f x v‖ ≤ C * t ^ α * t := by
    convert! hh using 1
    congr 1
    dsimp only [g]
    simp only [sub_self, map_zero, sub_zero, add_sub_cancel_left, map_smul]
    abel
  have hvb : t * ‖fderiv ℝ f x v‖ ≤ 2 * M + C * t ^ α * t := by
    calc
      _ = ‖t • fderiv ℝ f x v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      _ ≤ ‖f (x + t • v) - f x‖ + ‖f (x + t • v) - f x - t • fderiv ℝ f x v‖ :=
        norm_le_insert _ _
      _ ≤ (‖f (x + t • v)‖ + ‖f x‖) + C * t ^ α * t := add_le_add (norm_sub_le _ _) hrem
      _ ≤ 2 * M + C * t ^ α * t := by linarith [hb (x + t • v), hb x]
  apply (mul_le_mul_iff_left₀ ht).mp
  have he : (2 * M / t + C * t ^ α) * t = 2 * M + C * t ^ α * t := by field_simp
  rw [he]
  simpa only [mul_comm] using hvb

end Submission.Obl.Entropy__smooth_gaussian_transport
