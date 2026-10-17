import Submission.Obl.Entropy__smooth_gaussian_transport.CoordinateCubes

open MeasureTheory Set Filter BoxIntegral
open scoped Topology RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem ae_coordinate_dilation {m : ℕ} {P : E m → Prop}
    (hP : ∀ᵐ z ∂volume, P z) (c : E m) {r : ℝ} (hr : r ≠ 0) :
    ∀ᵐ y : Fin m → ℝ ∂volume, P (c + r • WithLp.toLp 2 y) :=
  (PiLp.volume_preserving_toLp (Fin m)).quasiMeasurePreserving.ae
    (ae_affine_dilation hP c hr)

theorem unitCoordinateBox_volume_pos (m : ℕ) :
    0 < volume (unitCoordinateBox m : Set (Fin m → ℝ)) := by
  rw [coordinate_cube_volume (ℓ := 2) (by norm_num)
    (fun _ => by norm_num [unitCoordinateBox])]
  exact ENNReal.ofReal_pos.mpr (by positivity)

theorem unit_ball_subset_box {m : ℕ} : Metric.ball (0 : E m) 1 ⊆ boxRegion (unitCoordinateBox m) := by
  have he : coordinateCenter (unitCoordinateBox m) = (0 : E m) := by
    ext i
    simp [coordinateCenter, unitCoordinateBox]
  rw [← he]
  exact coordinate_ball_subset_box _ (fun i => by norm_num [unitCoordinateBox])

theorem dilated_cube_mem_ball {m : ℕ} (c : E m) {r : ℝ} (hr : 0 < r)
    {y : Fin m → ℝ} (hy : y ∈ (unitCoordinateBox m : Set (Fin m → ℝ))) :
    c + r • WithLp.toLp 2 y ∈ Metric.ball c (r * (m + 6)) := by
  have hn := closedBoxRegion_unit_norm_le (m := m) (x := WithLp.toLp 2 y)
    (Box.coe_subset_Icc hy)
  rw [Metric.mem_ball, dist_eq_norm]
  have he : c + r • WithLp.toLp 2 y - c = r • WithLp.toLp 2 y := by abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  nlinarith

theorem dilated_cube_distance_le {m : ℕ} (c : E m) {r : ℝ} (hr : 0 ≤ r)
    {x y : Fin m → ℝ} (hx : x ∈ (unitCoordinateBox m : Set (Fin m → ℝ)))
    (hy : y ∈ (unitCoordinateBox m : Set (Fin m → ℝ))) :
    ‖(c + r • WithLp.toLp 2 y) - (c + r • WithLp.toLp 2 x)‖ ≤ 2 * m * r := by
  have hn := closedBoxRegion_dist_le (m := m) (J := unitCoordinateBox m)
    (ℓ := 2) (fun i => by norm_num [unitCoordinateBox])
    (x := WithLp.toLp 2 y) (y := WithLp.toLp 2 x)
    (Box.coe_subset_Icc hy) (Box.coe_subset_Icc hx)
  have he : (c + r • WithLp.toLp 2 y) - (c + r • WithLp.toLp 2 x) =
      r • (WithLp.toLp 2 y - WithLp.toLp 2 x) := by module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  rw [dist_eq_norm] at hn
  nlinarith [mul_le_mul_of_nonneg_left hn hr]

/-- An almost-everywhere assertion on the dilated coordinate cube holds on
the contained Euclidean ball. Both changes of variables preserve null sets. -/
theorem ae_ball_of_ae_dilated_cube {m : ℕ} {P : E m → Prop} (c : E m)
    {r : ℝ} (hr : 0 < r)
    (hP : ∀ᵐ y : Fin m → ℝ ∂volume.restrict (unitCoordinateBox m : Set (Fin m → ℝ)),
      P (c + r • WithLp.toLp 2 y)) :
    ∀ᵐ z ∂volume, z ∈ Metric.ball c r → P z := by
  have hP' := (ae_restrict_iff' (unitCoordinateBox m).measurableSet_coe).mp hP
  have hE : ∀ᵐ x : E m ∂volume, x ∈ boxRegion (unitCoordinateBox m) → P (c + r • x) := by
    have hh := (PiLp.volume_preserving_ofLp (Fin m)).quasiMeasurePreserving.ae hP'
    convert! hh using 1
  filter_upwards [ae_affine_dilation hE (-(r⁻¹ • c)) (inv_ne_zero hr.ne')] with z hz
  intro hzi
  let x : E m := -(r⁻¹ • c) + r⁻¹ • z
  have he : x = r⁻¹ • (z - c) := by dsimp [x]; module
  have hin : x ∈ Metric.ball (0 : E m) 1 := by
    rw [Metric.mem_ball, dist_zero_right, he, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
    have hh : ‖z - c‖ < r := Metric.mem_ball.mp hzi
    calc
      r⁻¹ * ‖z - c‖ < r⁻¹ * r := mul_lt_mul_of_pos_left hh (inv_pos.mpr hr)
      _ = 1 := inv_mul_cancel₀ hr.ne'
  have hcancel : c + r • x = z := by
    rw [he, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  have hh := hz (unit_ball_subset_box hin)
  rwa [hcancel] at hh

end Submission.Obl.Entropy__smooth_gaussian_transport
