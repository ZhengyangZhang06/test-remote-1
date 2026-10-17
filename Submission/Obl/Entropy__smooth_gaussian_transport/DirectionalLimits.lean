import Submission.Obl.Entropy__smooth_gaussian_transport.AeDirectionalBounds
import Submission.Obl.Entropy__smooth_gaussian_transport.SecondOrderExpansion

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem normalizedSecondDifference_error {m : ℕ} (u : E m → ℝ) (x p h : E m)
    (A : E m →L[ℝ] E m) :
    normalizedSecondDifference u h x - inner ℝ (A h) h / ‖h‖ ^ 2 =
      (quadraticError u x p A h + quadraticError u x p A (-h)) / ‖h‖ ^ 2 := by
  simp only [normalizedSecondDifference, secondDifference, symmetricAverage,
    quadraticError, map_neg, inner_neg_left, inner_neg_right, sub_eq_add_neg]
  ring

/-- Directional second differences converge at every point where the gradient
is differentiable, including when its derivative is only defined almost everywhere. -/
theorem tendsto_normalizedSecondDifference {m : ℕ} {u : E m → ℝ}
    (hu : Differentiable ℝ u) {x : E m} {A : E m →L[ℝ] E m}
    (hA : HasFDerivAt (gradient u) A x) {v : E m} (hv : ‖v‖ = 1)
    {ι : Type*} {l : Filter ι} {t : ι → ℝ}
    (ht : Tendsto t l (𝓝 0)) (ht0 : ∀ᶠ i in l, t i ≠ 0) :
    Tendsto (fun i => normalizedSecondDifference u (t i • v) x) l
      (𝓝 (inner ℝ (A v) v)) := by
  have hR := quadratic_expansion_of_hasFDerivAt_gradient hu hA
  have hstep : Tendsto (fun i => t i • v) l (𝓝 0) := by
    simpa only [zero_smul] using ht.smul_const v
  have hneg : Tendsto (fun i => -(t i • v)) l (𝓝 0) := by
    simpa only [neg_zero] using hstep.neg
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have herr := hR.bound (by positivity : 0 < ε / 3)
  filter_upwards [hstep.eventually herr, hneg.eventually herr, ht0] with i hp hn hti
  have hs : ‖t i • v‖ ^ 2 = (t i) ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs]
  have hspos : 0 < ‖t i • v‖ ^ 2 := by rw [hs]; exact sq_pos_of_ne_zero hti
  have he : inner ℝ (A (t i • v)) (t i • v) / ‖t i • v‖ ^ 2 = inner ℝ (A v) v := by
    rw [map_smul, real_inner_smul_left, real_inner_smul_right, hs]
    field_simp
  have hid := normalizedSecondDifference_error u x (gradient u x) (t i • v) A
  rw [he] at hid
  rw [Real.dist_eq, hid, abs_div, abs_of_pos hspos]
  apply (div_lt_iff₀ hspos).mpr
  have hp' : |quadraticError u x (gradient u x) A (t i • v)| ≤ ε / 3 * ‖t i • v‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, norm_pow, norm_norm, abs_norm] using hp
  have hn' : |quadraticError u x (gradient u x) A (-(t i • v))| ≤ ε / 3 * ‖t i • v‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, norm_pow, norm_norm, norm_neg, abs_norm] using hn
  have habs := abs_add_le (quadraticError u x (gradient u x) A (t i • v))
    (quadraticError u x (gradient u x) A (-(t i • v)))
  nlinarith [mul_pos hε hspos]

theorem ae_tendsto_normalizedSecondDifference {m : ℕ} {u : E m → ℝ}
    (hu : ContDiff ℝ 1 u) {L : NNReal} (hL : LipschitzWith L (gradient u))
    {v : E m} (hv : ‖v‖ = 1) {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝 0)) (ht0 : ∀ᶠ n in atTop, t n ≠ 0) :
    ∀ᵐ x ∂volume,
      Tendsto (fun n => normalizedSecondDifference u (t n • v) x) atTop
        (𝓝 (inner ℝ ((fderiv ℝ (gradient u) x) v) v)) := by
  filter_upwards [hL.ae_differentiableAt (μ := volume)] with x hx
  exact tendsto_normalizedSecondDifference hu.differentiable_one hx.hasFDerivAt hv ht ht0

/-- An essential upper bound in one unit direction bounds every sufficiently
short second difference in that direction. -/
theorem normalizedSecondDifference_smul_le_of_ae_bound {m : ℕ} {u : E m → ℝ}
    (hu : ContDiff ℝ 1 u) {L : NNReal} (hL : LipschitzWith L (gradient u))
    {Ω : Set (E m)} (hΩ : IsOpen Ω) (hc : Convex ℝ Ω)
    {v : E m} (hv : ‖v‖ = 1) {M : ℝ}
    (hH : ∀ᵐ y ∂volume, y ∈ Ω → inner ℝ ((fderiv ℝ (gradient u) y) v) v ≤ M)
    {t : ℝ} (ht : t ≠ 0) {x : E m} (hxm : x - t • v ∈ Ω) (hxp : x + t • v ∈ Ω) :
    normalizedSecondDifference u (t • v) x ≤ M := by
  have hv0 : v ≠ 0 := by intro he; rw [he, norm_zero] at hv; norm_num at hv
  have hstep : t • v ≠ 0 := by
    intro he
    have hn := congrArg norm he
    rw [norm_smul, Real.norm_eq_abs, hv, mul_one, norm_zero] at hn
    exact ht (abs_eq_zero.mp hn)
  apply normalizedSecondDifference_le_of_ae_hessian_bound hu hL hΩ hc hstep ?_ hxm hxp
  filter_upwards [hH] with y hy
  intro hyΩ
  have hh := mul_le_mul_of_nonneg_left (hy hyΩ) (sq_nonneg t)
  have hs : ‖t • v‖ ^ 2 = t ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs]
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right, hs]
  nlinarith only [hh]

end Submission.Obl.Entropy__smooth_gaussian_transport
