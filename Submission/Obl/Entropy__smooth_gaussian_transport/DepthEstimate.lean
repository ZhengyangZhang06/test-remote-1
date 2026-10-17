import Submission.Obl.Entropy__smooth_gaussian_transport.PolarPacking
import Submission.Obl.Entropy__smooth_gaussian_transport.AffineChange

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem translate_convex {m : ℕ} {u : E m → ℝ} (hu : ConvexOn ℝ univ u) (b : E m) :
    ConvexOn ℝ univ (fun x => u (x + b)) := by
  convert! hu.comp_affineMap (AffineEquiv.constVAdd ℝ (E m) b).toAffineMap using 1
  simp only [Function.comp_def, AffineEquiv.coe_toAffineMap,
    AffineEquiv.constVAdd_apply, vadd_eq_add, add_comm]

/-- A lower Alexandrov density bound forces depth at the center of every ball
on whose boundary the convex function is nonpositive. -/
theorem depth_at_center {m : ℕ} {u : E m → ℝ} (hu : ConvexOn ℝ univ u)
    (hdom : conjugateDomain u = univ) (c : E m) {r : ℝ} (hr : 0 < r)
    (hboundary : ∀ z ∈ Metric.sphere c r, u z ≤ 0)
    {l a : ℝ} (ha : 0 < a) (hal : a ^ m < l)
    (hmass : ∀ s : Set (E m), MeasurableSet s → s ⊆ Metric.closedBall c r →
      ENNReal.ofReal l * volume s ≤ alexandrovMeasure u s) :
    u c ≤ -(a / 2 * r ^ 2) := by
  have hb : ∀ z ∈ Metric.sphere (0 : E m) r, u (z + c) ≤ 0 := by
    intro z hz
    apply hboundary
    simpa only [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_right, sub_zero] using hz
  have hm : ∀ s : Set (E m), MeasurableSet s → s ⊆ Metric.closedBall (0 : E m) r →
      ENNReal.ofReal l * volume s ≤ alexandrovMeasure (fun z => u (z + c)) s := by
    intro s hs hsB
    have hs' : MeasurableSet ((fun z => z + c) '' s) :=
      (Homeomorph.addRight c).measurableEmbedding.measurableSet_image.mpr hs
    have hi : (fun z => z + c) '' s ⊆ Metric.closedBall c r := by
      rintro _ ⟨z, hz, rfl⟩
      simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hsB hz
    have h := hmass _ hs' hi
    rw [translate_alexandrov hu.locallyLipschitz.continuous hdom c hs]
    have hvol : volume ((fun z => z + c) '' s) = volume s := by
      rw [image_add_right, measure_preimage_add_right]
    rwa [hvol] at h
  have h := quadratic_upper_barrier (translate_convex hu c) (translate_conjugateDomain hdom c)
    hr hb ha hal hm (0 : E m) (Metric.mem_closedBall_self hr.le)
  simpa only [zero_add, norm_zero, zero_pow (by omega : 2 ≠ 0), zero_sub, mul_neg] using h

/-- On normalized sections with fixed density bounds, a point whose depth is
at least half the center's depth stays uniformly away from supporting planes. -/
theorem normalized_supporting_distance (m : ℕ) {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (B : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (u : E m → ℝ), ConvexOn ℝ univ u →
      conjugateDomain u = univ → ∀ (K : Set (E m)), IsCompact K →
      ∀ (c : E m), Metric.closedBall c r ⊆ K → K ⊆ Metric.closedBall c R →
      (∀ z ∈ K, u z ≤ 0) → (∀ z ∈ frontier K, 0 ≤ u z) →
      (∀ s : Set (E m), MeasurableSet s → s ⊆ K →
        (2 : ℝ≥0∞) * volume s ≤ alexandrovMeasure u s ∧
          alexandrovMeasure u s ≤ ENNReal.ofReal B * volume s) →
      ∀ (x e : E m), x ∈ K → 2 * u x ≤ u c → ‖e‖ = 1 →
      ∀ d : ℝ, 0 ≤ d → (∀ z ∈ K, inner ℝ e (z - x) ≤ d) → δ < d := by
  let M : ℝ≥0∞ := ENNReal.ofReal B * volume (Metric.closedBall (0 : E m) R)
  have hM : M ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (isCompact_closedBall (0 : E m) R).measure_lt_top.ne
  obtain ⟨δ, hδ, hdistance⟩ := uniform_supporting_distance m
    (D := 2 * R) (h := r ^ 2 / 4) (by positivity) (by positivity) hM
  refine ⟨δ, hδ, ?_⟩
  intro u hu hdom K hK c hinner houter hnonpos hboundary hmass x e hx hdepth he d hd hsupp
  have hcdepth : u c ≤ -(r ^ 2 / 2) := by
    have hlo (s : Set (E m)) (hs : MeasurableSet s) (hsB : s ⊆ Metric.closedBall c r) :
        ENNReal.ofReal 2 * volume s ≤ alexandrovMeasure u s := by
      simpa using (hmass s hs (hsB.trans hinner)).1
    have h := depth_at_center hu hdom c hr
      (fun z hz => hnonpos z (hinner (Metric.sphere_subset_closedBall hz)))
      (a := 1) (l := 2) zero_lt_one (by simp) hlo
    nlinarith
  have htotal : alexandrovMeasure u K ≤ M := by
    apply (hmass K hK.measurableSet (Subset.rfl)).2.trans
    have hvol : volume K ≤ volume (Metric.closedBall c R) := measure_mono houter
    rw [Measure.addHaar_closedBall_center volume] at hvol
    exact mul_le_mul_right hvol _
  have hKD : K ⊆ Metric.closedBall x (2 * R) := by
    intro z hz
    have hx' : dist x c ≤ R := houter hx
    have hz' : dist z c ≤ R := houter hz
    change dist z x ≤ 2 * R
    have ht := dist_triangle z c x
    rw [dist_comm c x] at ht
    linarith
  exact hdistance u hu hdom K hK hboundary htotal x e hx (by linarith) he hKD d hd hsupp

end Submission.Obl.Entropy__smooth_gaussian_transport
