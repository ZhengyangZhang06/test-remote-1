import Submission.Obl.Entropy__smooth_gaussian_transport.CoordinateCubes

open MeasureTheory Set Filter BoxIntegral
open scoped Topology RealInnerProductSpace NNReal ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem volume_coordinate_inter {m : ℕ} {S : Set (E m)} (hS : MeasurableSet S)
    (J : Box (Fin m)) :
    volume (WithLp.toLp 2 ⁻¹' S ∩ (J : Set (Fin m → ℝ))) = volume (S ∩ boxRegion J) := by
  have hh := (PiLp.volume_preserving_ofLp (Fin m)).measure_preimage
    ((hS.preimage (PiLp.volume_preserving_toLp (Fin m)).measurable).inter
      J.measurableSet_coe).nullMeasurableSet
  have he : WithLp.ofLp ⁻¹' (WithLp.toLp 2 ⁻¹' S ∩ (J : Set (Fin m → ℝ))) =
      S ∩ boxRegion J := by ext x; rfl
  rw [he] at hh
  exact hh.symm

theorem small_superlevel_of_sublevel {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℝ} (hf : Measurable f) {K : Set X}
    (hK : MeasurableSet K) (hfin : μ K ≠ ⊤) {κ t : ℝ}
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hgood : ENNReal.ofReal κ * μ K ≤ μ ({x | f x < t} ∩ K)) :
    μ ({x | t < f x} ∩ K) ≤ ENNReal.ofReal (1 - κ) * μ K := by
  have hg : MeasurableSet ({x | f x < t} ∩ K) := (measurableSet_lt hf measurable_const).inter hK
  have hd : Disjoint ({x | t < f x} ∩ K) ({x | f x < t} ∩ K) := by
    apply disjoint_left.mpr
    intro x hx hy
    have hx' : t < f x := hx.1
    have hy' : f x < t := hy.1
    exact lt_asymm hx' hy'
  have hsum : μ ({x | t < f x} ∩ K) + μ ({x | f x < t} ∩ K) ≤ μ K := by
    rw [← measure_union hd hg]
    exact measure_mono (union_subset inter_subset_right inter_subset_right)
  have hh : μ ({x | t < f x} ∩ K) + ENNReal.ofReal κ * μ K ≤ μ K := by
    apply le_trans _ hsum
    gcongr
  have he : ENNReal.ofReal (1 - κ) * μ K + ENNReal.ofReal κ * μ K = μ K := by
    rw [← add_mul, ← ENNReal.ofReal_add (sub_nonneg.mpr hκ1) hκ,
      sub_add_cancel, ENNReal.ofReal_one, one_mul]
  exact (ENNReal.add_le_add_iff_right (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)).mp
    (hh.trans_eq he.symm)

theorem sublevel_in_coordinate_cube {m : ℕ} (hm : 1 ≤ m) {u : E m → ℝ}
    (hu : Continuous u) {T η : ℝ}
    (h : HasSublevelMeasure u (Metric.closedBall 0 (m + 4)) T η)
    (hT : 1 ≤ T) (hη : 0 < η) {I J : Box (Fin m)}
    (hI : I ≤ unitCoordinateBox m) (hJI : J ≤ I) {r k : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hk : 1 ≤ k)
    (hJwidth : ∀ i, J.upper i - J.lower i = 2 * r)
    (hIwidth : ∀ i, I.upper i - I.lower i ≤ 4 * r)
    {x : E m} (hx : x ∈ closedBoxRegion I) (hux : u x ≤ k) :
    ENNReal.ofReal (η * r ^ m) ≤
      volume ({y : Fin m → ℝ | u (WithLp.toLp 2 y) < T ^ (2 * m + 1) * k} ∩
        (J : Set (Fin m → ℝ))) := by
  have hc : coordinateCenter J ∈ closedBoxRegion I :=
    closedBoxRegion_mono hJI (coordinateCenter_mem_closed J)
  have hxc : dist x (coordinateCenter J) ≤ 2 * (2 * m : ℕ) * r := by
    have hh := closedBoxRegion_dist_le hIwidth hx hc
    push_cast
    nlinarith
  have hregion : ∀ z ∈ segment ℝ x (coordinateCenter J),
      Metric.closedBall z (4 * r) ⊆ Metric.closedBall (0 : E m) (m + 4) := by
    intro z hz
    exact closedBoxRegion_thickening hI ((closedBoxRegion_convex I).segment_subset hx hc hz) hr1
  have hmeasure := h.measure_of_segment hT hη hr hr1 hk (N := 2 * m) (by omega) hxc hux hregion
  have hset : {z | dist z (coordinateCenter J) < r ∧ u z < T ^ (2 * m + 1) * k} ⊆
      {z | u z < T ^ (2 * m + 1) * k} ∩ boxRegion J := by
    intro z hz
    exact ⟨hz.2, coordinate_ball_subset_box J hJwidth hz.1⟩
  have hh := hmeasure.trans (measure_mono hset)
  rw [← volume_coordinate_inter (isOpen_lt hu continuous_const).measurableSet J] at hh
  exact hh

theorem cube_superlevel_small {m : ℕ} (hm : 1 ≤ m) {u : E m → ℝ}
    (hu : Continuous u) {T η κ : ℝ}
    (h : HasSublevelMeasure u (Metric.closedBall 0 (m + 4)) T η)
    (hT : 1 ≤ T) (hη : 0 < η) (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hκη : κ * (2 : ℝ) ^ m ≤ η) {I J : Box (Fin m)}
    (hI : I ≤ unitCoordinateBox m) (hJI : J ≤ I) {r k : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hk : 1 ≤ k)
    (hJwidth : ∀ i, J.upper i - J.lower i = 2 * r)
    (hIwidth : ∀ i, I.upper i - I.lower i ≤ 4 * r)
    {x : E m} (hx : x ∈ closedBoxRegion I) (hux : u x ≤ k) :
    volume ({y : Fin m → ℝ | T ^ (2 * m + 1) * k < u (WithLp.toLp 2 y)} ∩
        (J : Set (Fin m → ℝ))) ≤
      ENNReal.ofReal (1 - κ) * volume (J : Set (Fin m → ℝ)) := by
  apply small_superlevel_of_sublevel volume
    (hu.measurable.comp (PiLp.volume_preserving_toLp (Fin m)).measurable)
    J.measurableSet_coe (J.measure_coe_lt_top volume).ne hκ hκ1
  have hmass := sublevel_in_coordinate_cube hm hu h hT hη hI hJI hr hr1 hk hJwidth hIwidth hx hux
  apply le_trans _ hmass
  rw [coordinate_cube_volume (by positivity) hJwidth, ← ENNReal.ofReal_mul hκ]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_pow]
  have hh := mul_le_mul_of_nonneg_right hκη (pow_nonneg hr.le m)
  nlinarith

end Submission.Obl.Entropy__smooth_gaussian_transport
