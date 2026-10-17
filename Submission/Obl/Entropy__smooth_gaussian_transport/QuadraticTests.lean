import Submission.Obl.Entropy__smooth_gaussian_transport.QuadraticBarrier

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

private theorem exists_larger_with_pow_lt {a c : ℝ} {m : ℕ} (h : a ^ m < c) :
    ∃ b : ℝ, a < b ∧ b ^ m < c := by
  have hn : {b : ℝ | b ^ m < c} ∈ 𝓝 a :=
    (isOpen_lt (continuous_id.pow m) continuous_const).mem_nhds h
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨a + r / 2, by linarith, hb ?_⟩
  change |a + r / 2 - a| < r
  rw [show a + r / 2 - a = r / 2 by ring, abs_of_pos (by positivity)]
  linarith

private theorem exists_smaller_pos_with_lt_pow {a c : ℝ} {m : ℕ}
    (ha : 0 < a) (h : c < a ^ m) : ∃ b : ℝ, 0 < b ∧ b < a ∧ c < b ^ m := by
  have hn : {b : ℝ | 0 < b ∧ c < b ^ m} ∈ 𝓝 a :=
    ((isOpen_lt continuous_const continuous_id).inter
      (isOpen_lt continuous_const (continuous_id.pow m))).mem_nhds ⟨ha, h⟩
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hn
  have hh : a - r / 2 ∈ Metric.ball a r := by
    change |a - r / 2 - a| < r
    rw [show a - r / 2 - a = -(r / 2) by ring, abs_neg,
      abs_of_pos (by positivity)]
    linarith
  exact ⟨a - r / 2, (hb hh).1, by linarith, (hb hh).2⟩

/-- An upper quadratic test at a contact point has Monge–Ampère density
at least that of the convex solution. -/
theorem density_le_of_upper_quadratic_touch {m : ℕ} {u f : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ)
    (hf : Continuous f)
    (hMA : alexandrovMeasure u = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hzero : u 0 = 0) {a : ℝ} (ha : 0 < a)
    (htouch : ∀ᶠ x in 𝓝 (0 : E m), u x ≤ a / 2 * ‖x‖ ^ 2) :
    f 0 ≤ a ^ m := by
  by_contra hn
  obtain ⟨b, hab, hbpow⟩ := exists_larger_with_pow_lt (lt_of_not_ge hn)
  have hb : 0 < b := ha.trans hab
  obtain ⟨c, hbc, hcf⟩ := exists_between hbpow
  have hfnear : ∀ᶠ x in 𝓝 (0 : E m), c < f x := hf.continuousAt (lt_mem_nhds hcf)
  obtain ⟨r, hr, hnear⟩ := Metric.mem_nhds_iff.mp (htouch.and hfnear)
  let R := r / 2
  have hR : 0 < R := half_pos hr
  have hloc (z : E m) (hz : z ∈ Metric.closedBall (0 : E m) R) :
      u z ≤ a / 2 * ‖z‖ ^ 2 ∧ c < f z := by
    apply hnear
    change dist z 0 < r
    have hh : dist z 0 ≤ R := hz
    dsimp only [R] at hh
    linarith
  let q := quadraticBarrier (m := m) b ((a - b) / 2 * R ^ 2)
  have hbd : ∀ z ∈ frontier (Metric.closedBall (0 : E m) R), u z ≤ q z := by
    intro z hz
    have hzK := frontier_subset_closure hz
    rw [Metric.isClosed_closedBall.closure_eq] at hzK
    rw [frontier_closedBall _ hR.ne'] at hz
    have hnorm : ‖z‖ = R := by simpa using hz
    have h := (hloc z hzK).1
    simp only [q, quadraticBarrier, hnorm] at *
    nlinarith
  have hmass (s : Set (E m)) (hs : MeasurableSet s)
      (hsK : s ⊆ Metric.closedBall (0 : E m) R) (hpos : 0 < volume s) :
      alexandrovMeasure q s < alexandrovMeasure u s := by
    have hlower : ENNReal.ofReal c * volume s ≤ alexandrovMeasure u s := by
      rw [hMA, withDensity_apply _ hs]
      calc
        _ = ∫⁻ x in s, ENNReal.ofReal c := (setLIntegral_const _ _).symm
        _ ≤ _ := setLIntegral_mono hf.measurable.ennreal_ofReal
          (fun x hx => ENNReal.ofReal_le_ofReal (hloc x (hsK hx)).2.le)
    rw [quadraticBarrier_alexandrov hb _ hs]
    apply lt_of_lt_of_le _ hlower
    apply (ENNReal.mul_lt_mul_iff_left hpos.ne'
      ((measure_mono hsK).trans_lt (isCompact_closedBall (0 : E m) R).measure_lt_top).ne).mpr
    exact (ENNReal.ofReal_lt_ofReal_iff ((pow_pos hb _).trans hbc)).mpr hbc
  have hcomp := comparison_of_strict_mass (quadraticBarrier_convex hb.le _) hu
    (quadraticBarrier_conjugateDomain hb _) hdom (isCompact_closedBall (0 : E m) R)
    hbd hmass 0 (by simpa using hR.le)
  change u 0 ≤ q 0 at hcomp
  simp only [q, quadraticBarrier, hzero, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_add] at hcomp
  nlinarith [sq_pos_of_pos hR]

/-- A positive lower quadratic test has density at most that of the solution. -/
theorem density_ge_of_lower_quadratic_touch {m : ℕ} {u f : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ)
    (hf : Continuous f)
    (hMA : alexandrovMeasure u = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hzero : u 0 = 0) {a : ℝ} (ha : 0 < a)
    (htouch : ∀ᶠ x in 𝓝 (0 : E m), a / 2 * ‖x‖ ^ 2 ≤ u x) :
    a ^ m ≤ f 0 := by
  by_contra hn
  obtain ⟨b, hb, hba, hbpow⟩ := exists_smaller_pos_with_lt_pow ha (lt_of_not_ge hn)
  obtain ⟨c, hfc, hcb⟩ := exists_between hbpow
  have hfnear : ∀ᶠ x in 𝓝 (0 : E m), f x < c := hf.continuousAt (gt_mem_nhds hfc)
  obtain ⟨r, hr, hnear⟩ := Metric.mem_nhds_iff.mp (htouch.and hfnear)
  let R := r / 2
  have hR : 0 < R := half_pos hr
  have hloc (z : E m) (hz : z ∈ Metric.closedBall (0 : E m) R) :
      a / 2 * ‖z‖ ^ 2 ≤ u z ∧ f z < c := by
    apply hnear
    change dist z 0 < r
    have hh : dist z 0 ≤ R := hz
    dsimp only [R] at hh
    linarith
  let q := quadraticBarrier (m := m) b ((a - b) / 2 * R ^ 2)
  have hbd : ∀ z ∈ frontier (Metric.closedBall (0 : E m) R), q z ≤ u z := by
    intro z hz
    have hzK := frontier_subset_closure hz
    rw [Metric.isClosed_closedBall.closure_eq] at hzK
    rw [frontier_closedBall _ hR.ne'] at hz
    have hnorm : ‖z‖ = R := by simpa using hz
    have h := (hloc z hzK).1
    simp only [q, quadraticBarrier, hnorm] at *
    nlinarith
  have hmass (s : Set (E m)) (hs : MeasurableSet s)
      (hsK : s ⊆ Metric.closedBall (0 : E m) R) (hpos : 0 < volume s) :
      alexandrovMeasure u s < alexandrovMeasure q s := by
    have hupper : alexandrovMeasure u s ≤ ENNReal.ofReal c * volume s := by
      rw [hMA, withDensity_apply _ hs]
      calc
        _ ≤ ∫⁻ x in s, ENNReal.ofReal c := setLIntegral_mono measurable_const
          (fun x hx => ENNReal.ofReal_le_ofReal (hloc x (hsK hx)).2.le)
        _ = _ := setLIntegral_const _ _
    rw [quadraticBarrier_alexandrov hb _ hs]
    apply hupper.trans_lt
    apply (ENNReal.mul_lt_mul_iff_left hpos.ne'
      ((measure_mono hsK).trans_lt (isCompact_closedBall (0 : E m) R).measure_lt_top).ne).mpr
    exact (ENNReal.ofReal_lt_ofReal_iff (pow_pos hb _)).mpr hcb
  have hcomp := comparison_of_strict_mass hu (quadraticBarrier_convex hb.le _)
    hdom (quadraticBarrier_conjugateDomain hb _) (isCompact_closedBall (0 : E m) R)
    hbd hmass 0 (by simpa using hR.le)
  change q 0 ≤ u 0 at hcomp
  simp only [q, quadraticBarrier, hzero, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_add] at hcomp
  nlinarith [sq_pos_of_pos hR]

end Submission.Obl.Entropy__smooth_gaussian_transport
