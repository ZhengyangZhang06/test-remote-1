import Submission.Obl.Entropy__smooth_gaussian_transport.Comparison

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Slopes of affine functions with value zero at `x` that stay strictly below `h` on `K`. -/
def strictPolar {m : ℕ} (K : Set (E m)) (x : E m) (h : ℝ) : Set (E m) :=
  {p | ∀ z ∈ K, inner ℝ p (z - x) < h}

/-- Sliding a plane with a slope in the polar set produces an interior supporting point. -/
theorem strictPolar_subset_subgradientImage {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) {K : Set (E m)} (hK : IsCompact K)
    (hboundary : ∀ z ∈ frontier K, 0 ≤ u z) {x : E m} (hx : x ∈ K) :
    strictPolar K x (-u x) ⊆ subgradientImage u {z | z ∈ K ∧ u z < 0} := by
  intro p hp
  have hg : ∀ z ∈ frontier K, u x + inner ℝ p (z - x) < u z := by
    intro z hz
    have h := hp z (hK.isClosed.closure_eq ▸ hz.1)
    linarith [hboundary z hz]
  obtain ⟨z, hzint, hzp, hz⟩ := supporting_point_of_boundary_gap hu hK hx hg
  refine ⟨z, ⟨interior_subset hzint, ?_⟩, hzp⟩
  have h := hp z (interior_subset hzint)
  rw [inner_sub_right] at h
  linarith

/-- An Aleksandrov estimate in polar form. -/
theorem alexandrov_polar_bound {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ)
    {K : Set (E m)} (hK : IsCompact K)
    (hboundary : ∀ z ∈ frontier K, 0 ≤ u z) {x : E m} (hx : x ∈ K) :
    volume (strictPolar K x (-u x)) ≤ alexandrovMeasure u {z | z ∈ K ∧ u z < 0} := by
  have hs : MeasurableSet {z | z ∈ K ∧ u z < 0} :=
    hK.measurableSet.inter (isOpen_lt hu.locallyLipschitz.continuous continuous_const).measurableSet
  rw [alexandrovMeasure_apply hu.locallyLipschitz.continuous hdom hs]
  exact measure_mono (strictPolar_subset_subgradientImage hu hK hboundary hx)

theorem ball_subset_strictPolar {m : ℕ} {K : Set (E m)} {x : E m} {D h : ℝ}
    (hD : 0 < D) (hK : K ⊆ Metric.closedBall x D) :
    Metric.ball (0 : E m) (h / D) ⊆ strictPolar K x h := by
  intro p hp z hz
  have hp' : ‖p‖ < h / D := by simpa using hp
  have hz' : ‖z - x‖ ≤ D := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hK hz
  calc
    inner ℝ p (z - x) ≤ ‖p‖ * ‖z - x‖ := real_inner_le_norm _ _
    _ ≤ ‖p‖ * D := mul_le_mul_of_nonneg_left hz' (norm_nonneg p)
    _ < h := (lt_div_iff₀ hD).mp hp'

/-- A quantitative maximum principle using any ball containing the compact region. -/
theorem alexandrov_ball_bound {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ)
    {K : Set (E m)} (hK : IsCompact K)
    (hboundary : ∀ z ∈ frontier K, 0 ≤ u z) {x : E m} (hx : x ∈ K)
    {D : ℝ} (hD : 0 < D) (hKD : K ⊆ Metric.closedBall x D) :
    volume (Metric.ball (0 : E m) (-u x / D)) ≤ alexandrovMeasure u K := by
  exact (measure_mono (ball_subset_strictPolar hD hKD)).trans
    ((alexandrov_polar_bound hu hdom hK hboundary hx).trans
      (measure_mono (fun _ h => h.1)))

theorem maximum_principle_zero_mass {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ)
    {K : Set (E m)} (hK : IsCompact K)
    (hboundary : ∀ z ∈ frontier K, 0 ≤ u z) (hzero : alexandrovMeasure u K = 0) :
    ∀ x ∈ K, 0 ≤ u x := by
  intro x hx
  by_contra hn
  have hneg : u x < 0 := lt_of_not_ge hn
  obtain ⟨D, hD⟩ := hK.isBounded.subset_closedBall x
  have hDD : K ⊆ Metric.closedBall x (max 1 D) := hD.trans (Metric.closedBall_subset_closedBall
    (le_max_right _ _))
  have hpos : 0 < max 1 D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have he := alexandrov_ball_bound hu hdom hK hboundary hx hpos hDD
  rw [hzero] at he
  have hp : 0 < volume (Metric.ball (0 : E m) (-u x / max 1 D)) :=
    Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr (div_pos (neg_pos.mpr hneg) hpos))
  exact (not_lt_of_ge he) hp

end Submission.Obl.Entropy__smooth_gaussian_transport
