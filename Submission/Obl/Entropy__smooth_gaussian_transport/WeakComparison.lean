import Submission.Obl.Entropy__smooth_gaussian_transport.DensityNormalization

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Positive local density bounds allow equality in the measure comparison
principle, by slightly increasing the comparison potential's height scale. -/
theorem comparison_of_mass_le_of_bounds {m : ℕ} (hm : 1 ≤ m) {u v : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hv : ConvexOn ℝ univ v)
    (hdu : conjugateDomain u = univ) (hdv : conjugateDomain v = univ)
    {K : Set (E m)} (hK : IsCompact K) {l U : ℝ} (hl : 0 < l)
    (hb : ∀ s : Set (E m), MeasurableSet s → s ⊆ K →
      ENNReal.ofReal l * volume s ≤ alexandrovMeasure v s ∧
        alexandrovMeasure v s ≤ ENNReal.ofReal U * volume s)
    (hboundary : ∀ x ∈ frontier K, v x ≤ u x)
    (hmass : ∀ s : Set (E m), MeasurableSet s → s ⊆ K →
      alexandrovMeasure u s ≤ alexandrovMeasure v s) :
    ∀ x ∈ K, v x ≤ u x := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image hv.locallyLipschitz.continuous.continuousOn
  intro x hx
  by_contra hn
  have hxgap : u x < v x := lt_of_not_ge hn
  have hCx : v x ≤ C := hC (mem_image_of_mem v hx)
  let ε := (v x - u x) / (2 * (C - v x + 1))
  have hden : 0 < 2 * (C - v x + 1) := by linarith
  have hε : 0 < ε := div_pos (sub_pos.mpr hxgap) hden
  have heq : ε * (2 * (C - v x + 1)) = v x - u x := div_mul_cancel₀ _ hden.ne'
  have hscale : 0 < 1 + ε := by linarith
  let q := tilt (fun z => (1 + ε) * v z) 0 (ε * C)
  have hqc : ConvexOn ℝ univ q := tilt_convex (hv.smul hscale.le) 0 (ε * C)
  have hqd : conjugateDomain q = univ :=
    tilt_conjugateDomain (positiveScale_conjugateDomain hdv hscale) 0 (ε * C)
  have hqval (z : E m) : q z = v z - ε * (C - v z) := by
    simp only [q, tilt, inner_zero_left, sub_zero]
    ring
  have hbd : ∀ z ∈ frontier K, q z ≤ u z := by
    intro z hz
    have hzK : z ∈ K := by
      have hh := frontier_subset_closure hz
      rwa [hK.isClosed.closure_eq] at hh
    rw [hqval]
    have hCz : v z ≤ C := hC (mem_image_of_mem v hzK)
    exact (sub_le_self _ (mul_nonneg hε.le (sub_nonneg.mpr hCz))).trans (hboundary z hz)
  have hstrict (s : Set (E m)) (hs : MeasurableSet s) (hsK : s ⊆ K)
      (hpos : 0 < volume s) : alexandrovMeasure u s < alexandrovMeasure q s := by
    have hvol : volume s < ⊤ := (measure_mono hsK).trans_lt hK.measure_lt_top
    have hposv : 0 < alexandrovMeasure v s :=
      (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hl).ne' hpos.ne').trans_le (hb s hs hsK).1
    have hfinv : alexandrovMeasure v s < ⊤ := (hb s hs hsK).2.trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvol)
    have hp : (1 : ℝ) < (1 + ε) ^ m := one_lt_pow₀ (by linarith) (by omega)
    have hp' : (1 : ℝ≥0∞) < ENNReal.ofReal ((1 + ε) ^ m) := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff (zero_lt_one.trans hp)).mpr hp
    change alexandrovMeasure u s < alexandrovMeasure
      (tilt (fun z => (1 + ε) * v z) 0 (ε * C)) s
    rw [tilt_alexandrovMeasure (u := fun z => (1 + ε) * v z)
      (continuous_const.mul hv.locallyLipschitz.continuous)
      (positiveScale_conjugateDomain hdv hscale) 0 (ε * C),
      positiveScale_alexandrov hv.locallyLipschitz.continuous hdv hscale hs]
    apply (hmass s hs hsK).trans_lt
    have hh := (ENNReal.mul_lt_mul_iff_left hposv.ne' hfinv.ne).mpr hp'
    simpa only [one_mul] using hh
  have hcomp := comparison_of_strict_mass hu hqc hdu hqd hK hbd hstrict x hx
  rw [hqval] at hcomp
  nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hCx)]

theorem comparison_of_mass_le {m : ℕ} (hm : 1 ≤ m) {u v : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hv : ConvexOn ℝ univ v)
    (hdu : conjugateDomain u = univ) (hdv : conjugateDomain v = univ)
    (hMv : LocalDensityBounds v) {K : Set (E m)} (hK : IsCompact K)
    (hboundary : ∀ x ∈ frontier K, v x ≤ u x)
    (hmass : ∀ s : Set (E m), MeasurableSet s → s ⊆ K →
      alexandrovMeasure u s ≤ alexandrovMeasure v s) :
    ∀ x ∈ K, v x ≤ u x := by
  obtain ⟨l, U, hl, _, hb⟩ := hMv K hK
  exact comparison_of_mass_le_of_bounds hm hu hv hdu hdv hK hl hb hboundary hmass

/-- The Dirichlet problem has at most one convex solution with positive local
Alexandrov density bounds, among potentials finite on the whole space. -/
theorem eqOn_of_alexandrovMeasure_eq {m : ℕ} (hm : 1 ≤ m) {u v : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hv : ConvexOn ℝ univ v)
    (hdu : conjugateDomain u = univ) (hdv : conjugateDomain v = univ)
    (hMu : LocalDensityBounds u) (hMv : LocalDensityBounds v)
    {K : Set (E m)} (hK : IsCompact K) (hboundary : EqOn u v (frontier K))
    (hmass : ∀ s : Set (E m), MeasurableSet s → s ⊆ K →
      alexandrovMeasure u s = alexandrovMeasure v s) : EqOn u v K := by
  have h₁ := comparison_of_mass_le hm hu hv hdu hdv hMv hK
    (fun x hx => (hboundary hx).ge) (fun s hs hsK => (hmass s hs hsK).le)
  have h₂ := comparison_of_mass_le hm hv hu hdv hdu hMu hK
    (fun x hx => (hboundary hx).le) (fun s hs hsK => (hmass s hs hsK).ge)
  exact fun x hx => le_antisymm (h₂ x hx) (h₁ x hx)

end Submission.Obl.Entropy__smooth_gaussian_transport
