import Submission.Obl.Entropy__smooth_gaussian_transport.WeakComparison

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem positiveScale_mass_bounds {m : ℕ} {v : E m → ℝ}
    (hv : Continuous v) (hdv : conjugateDomain v = univ)
    {K : Set (E m)} {l U a : ℝ} (ha : 0 < a)
    (hb : ∀ s : Set (E m), MeasurableSet s → s ⊆ K →
      ENNReal.ofReal l * volume s ≤ alexandrovMeasure v s ∧
        alexandrovMeasure v s ≤ ENNReal.ofReal U * volume s) :
    ∀ s : Set (E m), MeasurableSet s → s ⊆ K →
      ENNReal.ofReal (a ^ m * l) * volume s ≤ alexandrovMeasure (fun x => a * v x) s ∧
        alexandrovMeasure (fun x => a * v x) s ≤ ENNReal.ofReal (a ^ m * U) * volume s := by
  intro s hs hsK
  rw [positiveScale_alexandrov hv hdv ha hs]
  constructor
  · simpa only [ENNReal.ofReal_mul (pow_nonneg ha.le m), mul_assoc] using
      mul_le_mul_right (hb s hs hsK).1 (ENNReal.ofReal (a ^ m))
  · simpa only [ENNReal.ofReal_mul (pow_nonneg ha.le m), mul_assoc] using
      mul_le_mul_right (hb s hs hsK).2 (ENNReal.ofReal (a ^ m))

/-- Scaling the density bounds scales zero-boundary solutions in the opposite
order, with no strictness assumption on the inequalities between measures. -/
theorem scale_sandwich_of_mass_bounds {m : ℕ} (hm : 1 ≤ m) {u v : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hv : ConvexOn ℝ univ v)
    (hdu : conjugateDomain u = univ) (hdv : conjugateDomain v = univ)
    {K : Set (E m)} (hK : IsCompact K)
    (hu0 : ∀ x ∈ frontier K, u x = 0) (hv0 : ∀ x ∈ frontier K, v x = 0)
    {a b l U : ℝ} (ha : 0 < a) (hb : 0 < b) (hl : 0 < l)
    (hMv : ∀ s : Set (E m), MeasurableSet s → s ⊆ K →
      ENNReal.ofReal l * volume s ≤ alexandrovMeasure v s ∧
        alexandrovMeasure v s ≤ ENNReal.ofReal U * volume s)
    (hmass : ∀ s : Set (E m), MeasurableSet s → s ⊆ K →
      ENNReal.ofReal (a ^ m) * alexandrovMeasure v s ≤ alexandrovMeasure u s ∧
        alexandrovMeasure u s ≤ ENNReal.ofReal (b ^ m) * alexandrovMeasure v s) :
    ∀ x ∈ K, b * v x ≤ u x ∧ u x ≤ a * v x := by
  have hMu (s : Set (E m)) (hs : MeasurableSet s) (hsK : s ⊆ K) :
      ENNReal.ofReal (a ^ m * l) * volume s ≤ alexandrovMeasure u s ∧
        alexandrovMeasure u s ≤ ENNReal.ofReal (b ^ m * U) * volume s := by
    constructor
    · have hh := (mul_le_mul_right (hMv s hs hsK).1 (ENNReal.ofReal (a ^ m))).trans
        (hmass s hs hsK).1
      simpa only [ENNReal.ofReal_mul (pow_nonneg ha.le m), mul_assoc] using hh
    · have hh := (hmass s hs hsK).2.trans
        (mul_le_mul_right (hMv s hs hsK).2 (ENNReal.ofReal (b ^ m)))
      simpa only [ENNReal.ofReal_mul (pow_nonneg hb.le m), mul_assoc] using hh
  have hlow := comparison_of_mass_le_of_bounds hm hu (hv.smul hb.le) hdu
    (positiveScale_conjugateDomain hdv hb) hK (mul_pos (pow_pos hb m) hl)
    (positiveScale_mass_bounds hv.locallyLipschitz.continuous hdv hb hMv)
    (by intro x hx; simp only [smul_eq_mul, hu0 x hx, hv0 x hx, mul_zero, le_refl])
    (by
      intro s hs hsK
      simp only [smul_eq_mul]
      rw [positiveScale_alexandrov hv.locallyLipschitz.continuous hdv hb hs]
      exact (hmass s hs hsK).2)
  have hupp := comparison_of_mass_le_of_bounds hm (hv.smul ha.le) hu
    (positiveScale_conjugateDomain hdv ha) hdu hK (mul_pos (pow_pos ha m) hl) hMu
    (by intro x hx; simp only [smul_eq_mul, hu0 x hx, hv0 x hx, mul_zero, le_refl])
    (by
      intro s hs hsK
      simp only [smul_eq_mul]
      rw [positiveScale_alexandrov hv.locallyLipschitz.continuous hdv ha hs]
      exact (hmass s hs hsK).1)
  exact fun x hx => ⟨hlow x hx, hupp x hx⟩

/-- Relative Monge–Ampère measure errors give a uniform error estimate for
solutions with zero boundary data. -/
theorem relative_density_stability {m : ℕ} (hm : 1 ≤ m) {u v : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hv : ConvexOn ℝ univ v)
    (hdu : conjugateDomain u = univ) (hdv : conjugateDomain v = univ)
    {K : Set (E m)} (hK : IsCompact K)
    (hu0 : ∀ x ∈ frontier K, u x = 0) (hv0 : ∀ x ∈ frontier K, v x = 0)
    {ε l U : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) (hl : 0 < l)
    (hMv : ∀ s : Set (E m), MeasurableSet s → s ⊆ K →
      ENNReal.ofReal l * volume s ≤ alexandrovMeasure v s ∧
        alexandrovMeasure v s ≤ ENNReal.ofReal U * volume s)
    (hmass : ∀ s : Set (E m), MeasurableSet s → s ⊆ K →
      ENNReal.ofReal ((1 - ε) ^ m) * alexandrovMeasure v s ≤ alexandrovMeasure u s ∧
        alexandrovMeasure u s ≤ ENNReal.ofReal ((1 + ε) ^ m) * alexandrovMeasure v s) :
    ∀ x ∈ K, |u x - v x| ≤ ε * |v x| := by
  have hsand := scale_sandwich_of_mass_bounds hm hu hv hdu hdv hK hu0 hv0
    (sub_pos.mpr hε1) (by linarith : 0 < 1 + ε) hl hMv hmass
  intro x hx
  obtain ⟨hlo, hhi⟩ := hsand x hx
  have habs := mul_le_mul_of_nonneg_left (neg_abs_le (v x)) hε
  apply abs_le.mpr
  constructor <;> nlinarith

end Submission.Obl.Entropy__smooth_gaussian_transport
