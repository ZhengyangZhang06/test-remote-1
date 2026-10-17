import Submission.Obl.Entropy__smooth_gaussian_transport.SublevelPropagation
import Submission.Obl.Entropy__smooth_gaussian_transport.BoxMeasureDecay
import Submission.Obl.Entropy__smooth_gaussian_transport.Normalization

open MeasureTheory Set Filter BoxIntegral
open scoped Topology RealInnerProductSpace NNReal ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

def unitCoordinateBox (m : ℕ) : Box (Fin m) :=
  ⟨fun _ => -1, fun _ => 1, fun _ => by norm_num⟩

def IsCoordinateCube {m : ℕ} (J : Box (Fin m)) : Prop :=
  ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ i, J.upper i - J.lower i = ℓ

def boxRegion {m : ℕ} (J : Box (Fin m)) : Set (E m) :=
  WithLp.ofLp ⁻¹' (J : Set (Fin m → ℝ))

def closedBoxRegion {m : ℕ} (J : Box (Fin m)) : Set (E m) :=
  WithLp.ofLp ⁻¹' J.Icc

noncomputable def coordinateCenter {m : ℕ} (J : Box (Fin m)) : E m :=
  WithLp.toLp 2 (fun i => (J.lower i + J.upper i) / 2)

theorem unitCoordinateBox_isCube (m : ℕ) : IsCoordinateCube (unitCoordinateBox m) :=
  ⟨2, by norm_num, fun _ => by norm_num [unitCoordinateBox]⟩

theorem IsCoordinateCube.split {m : ℕ} {J : Box (Fin m)} (hJ : IsCoordinateCube J)
    (s : Set (Fin m)) : IsCoordinateCube (J.splitCenterBox s) := by
  obtain ⟨ℓ, hℓ, hwidth⟩ := hJ
  exact ⟨ℓ / 2, half_pos hℓ, fun i => by rw [Box.upper_sub_lower_splitCenterBox, hwidth]⟩

theorem boxRegion_measurable {m : ℕ} (J : Box (Fin m)) : MeasurableSet (boxRegion J) :=
  J.measurableSet_coe.preimage (PiLp.volume_preserving_ofLp (Fin m)).measurable

theorem boxRegion_volume {m : ℕ} (J : Box (Fin m)) :
    volume (boxRegion J) = volume (J : Set (Fin m → ℝ)) :=
  (PiLp.volume_preserving_ofLp (Fin m)).measure_preimage J.measurableSet_coe.nullMeasurableSet

theorem boxRegion_subset_closed {m : ℕ} (J : Box (Fin m)) :
    boxRegion J ⊆ closedBoxRegion J := fun _ hx => Box.coe_subset_Icc hx

theorem coordinateCenter_mem_closed {m : ℕ} (J : Box (Fin m)) :
    coordinateCenter J ∈ closedBoxRegion J := by
  constructor <;> intro i <;> change _ ≤ _
  · change J.lower i ≤ (J.lower i + J.upper i) / 2
    linarith [J.lower_lt_upper i]
  · change (J.lower i + J.upper i) / 2 ≤ J.upper i
    linarith [J.lower_lt_upper i]

theorem closedBoxRegion_convex {m : ℕ} (J : Box (Fin m)) :
    Convex ℝ (closedBoxRegion J) := by
  exact (convex_Icc J.lower J.upper).linear_preimage (EuclideanSpace.equiv (Fin m) ℝ).toLinearMap

theorem closedBoxRegion_mono {m : ℕ} {I J : Box (Fin m)} (h : I ≤ J) :
    closedBoxRegion I ⊆ closedBoxRegion J := fun _ hx => (Box.le_iff_Icc.mp h) hx

theorem closedBoxRegion_unit_norm_le {m : ℕ} {x : E m}
    (hx : x ∈ closedBoxRegion (unitCoordinateBox m)) : ‖x‖ ≤ m := by
  have hb (i : Fin m) : |x i| ≤ 1 :=
    abs_le.mpr ⟨hx.1 i, hx.2 i⟩
  calc
    ‖x‖ ≤ ∑ i, |x i| := norm_le_sum_abs_coordinates x
    _ ≤ ∑ _i : Fin m, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hb i)
    _ = m := by simp

theorem coordinate_ball_subset_box {m : ℕ} (J : Box (Fin m)) {r : ℝ}
    (hwidth : ∀ i, J.upper i - J.lower i = 2 * r) :
    Metric.ball (coordinateCenter J) r ⊆ boxRegion J := by
  intro x hx i
  have hn : ‖x - coordinateCenter J‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hi : |x i - (J.lower i + J.upper i) / 2| < r := by
    have hh := (PiLp.norm_apply_le (x - coordinateCenter J) i).trans_lt hn
    exact hh
  have hlo := (abs_lt.mp hi).1
  have hhi := (abs_lt.mp hi).2
  have hw := hwidth i
  exact ⟨by linarith, by linarith⟩

theorem closedBoxRegion_dist_le {m : ℕ} {J : Box (Fin m)} {ℓ : ℝ}
    (hwidth : ∀ i, J.upper i - J.lower i ≤ ℓ) {x y : E m}
    (hx : x ∈ closedBoxRegion J) (hy : y ∈ closedBoxRegion J) :
    dist x y ≤ m * ℓ := by
  have hb (i : Fin m) : |(x - y) i| ≤ ℓ := by
    change |x i - y i| ≤ ℓ
    have hw := hwidth i
    have hxlo := hx.1 i
    have hxhi := hx.2 i
    have hylo := hy.1 i
    have hyhi := hy.2 i
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    dist x y = ‖x - y‖ := dist_eq_norm _ _
    _ ≤ ∑ i, |(x - y) i| := norm_le_sum_abs_coordinates _
    _ ≤ ∑ _i : Fin m, ℓ := Finset.sum_le_sum (fun i _ => hb i)
    _ = m * ℓ := by simp

theorem coordinate_cube_volume {m : ℕ} {J : Box (Fin m)} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hwidth : ∀ i, J.upper i - J.lower i = ℓ) :
    volume (J : Set (Fin m → ℝ)) = ENNReal.ofReal (ℓ ^ m) := by
  rw [Box.coe_eq_pi, Real.volume_pi_Ioc]
  simp only [hwidth, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow hℓ m).symm

theorem closedBoxRegion_thickening {m : ℕ} {J : Box (Fin m)}
    (hJ : J ≤ unitCoordinateBox m) {z : E m} (hz : z ∈ closedBoxRegion J)
    {r : ℝ} (hr : r ≤ 1) :
    Metric.closedBall z (4 * r) ⊆ Metric.closedBall (0 : E m) (m + 4) := by
  intro y hy
  have hz' := closedBoxRegion_unit_norm_le (closedBoxRegion_mono hJ hz)
  have hy' : dist y z ≤ 4 * r := hy
  rw [Metric.mem_closedBall, dist_zero_right]
  have hh := dist_triangle y z 0
  simp only [dist_zero_right] at hh
  linarith

theorem coordinate_cube_side_le_two {m : ℕ} (hm : 1 ≤ m) {J : Box (Fin m)}
    (hJ : J ≤ unitCoordinateBox m) {ℓ : ℝ}
    (hwidth : ∀ i, J.upper i - J.lower i = ℓ) : ℓ ≤ 2 := by
  let i : Fin m := ⟨0, by omega⟩
  have hlo : -1 ≤ J.lower i := (Box.le_iff_bounds.mp hJ).1 i
  have hhi : J.upper i ≤ 1 := (Box.le_iff_bounds.mp hJ).2 i
  have hw := hwidth i
  linarith

end Submission.Obl.Entropy__smooth_gaussian_transport
