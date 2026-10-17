import Submission.Obl.Entropy__smooth_gaussian_transport.FiniteDifferenceMaximum

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def scaledTilt {m : ℕ} (u : E m → ℝ) (p : E m) (c : ℝ) (x : E m) : ℝ :=
  c * u x - (c - 1) * inner ℝ p x

theorem scaledTilt_eq_tilt {m : ℕ} (u : E m → ℝ) (p : E m) (c : ℝ) :
    scaledTilt u p c = tilt (fun x => c * u x) ((c - 1) • p) 0 := by
  funext x
  simp only [scaledTilt, tilt, real_inner_smul_left, sub_zero]

theorem scaledTilt_convex {m : ℕ} {u : E m → ℝ} (hu : ConvexOn ℝ univ u)
    (p : E m) {c : ℝ} (hc : 0 ≤ c) : ConvexOn ℝ univ (scaledTilt u p c) := by
  rw [scaledTilt_eq_tilt]
  exact tilt_convex (hu.smul hc) _ _

theorem scaledTilt_conjugateDomain {m : ℕ} {u : E m → ℝ} (hdom : conjugateDomain u = univ)
    (p : E m) {c : ℝ} (hc : 0 < c) : conjugateDomain (scaledTilt u p c) = univ := by
  rw [scaledTilt_eq_tilt]
  exact tilt_conjugateDomain (positiveScale_conjugateDomain hdom hc) _ _

theorem scaledTilt_contDiff {m : ℕ} {u : E m → ℝ} {n : WithTop ENat}
    (hu : ContDiff ℝ n u) (p : E m) (c : ℝ) : ContDiff ℝ n (scaledTilt u p c) :=
  (contDiff_const.mul hu).sub (contDiff_const.mul (contDiff_const.inner ℝ contDiff_id))

theorem gradient_scaledTilt {m : ℕ} {u : E m → ℝ} (hu : Differentiable ℝ u)
    (p : E m) (c : ℝ) (x : E m) :
    gradient (scaledTilt u p c) x = c • gradient u x - (c - 1) • p := by
  have hd : HasFDerivAt (scaledTilt u p c)
      (c • fderiv ℝ u x - (c - 1) • innerSL ℝ p) x :=
    ((hu x).hasFDerivAt.const_mul c).sub ((innerSL ℝ p).hasFDerivAt.const_mul (c - 1))
  apply (InnerProductSpace.toDual ℝ (E m)).injective
  simp only [toDual_gradient, map_sub, map_smul]
  rw [hd.fderiv]
  congr 2

theorem scaledTilt_alexandrov {m : ℕ} {u : E m → ℝ} (hu : Continuous u)
    (hdom : conjugateDomain u = univ) (p : E m) {c : ℝ} (hc : 0 < c) :
    alexandrovMeasure (scaledTilt u p c) = ENNReal.ofReal (c ^ m) • alexandrovMeasure u := by
  ext s hs
  rw [scaledTilt_eq_tilt, tilt_alexandrovMeasure (u := fun x => c * u x)
    (continuous_const.mul hu) (positiveScale_conjugateDomain hdom hc),
    positiveScale_alexandrov hu hdom hc hs, Measure.smul_apply, smul_eq_mul]

theorem scaledTilt_alexandrov_density {m : ℕ} {u f : E m → ℝ} (hu : Continuous u)
    (hdom : conjugateDomain u = univ)
    (hMA : alexandrovMeasure u = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (p : E m) {c : ℝ} (hc : 0 < c) :
    alexandrovMeasure (scaledTilt u p c) =
      volume.withDensity (fun x => ENNReal.ofReal (c ^ m * f x)) := by
  rw [scaledTilt_alexandrov hu hdom p hc, hMA,
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.ofReal_mul (pow_pos hc _).le]

theorem convex_value_le_radial_dilation {m : ℕ} {V : E m → ℝ}
    (hV : ConvexOn ℝ univ V) {p : E m} (hp : ∀ y, V p ≤ V y)
    {c : ℝ} (hc : 1 ≤ c) (y : E m) : V y ≤ V (c • y - (c - 1) • p) := by
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hinv : 0 < c⁻¹ := inv_pos.mpr hcpos
  have hle : c⁻¹ ≤ 1 := (inv_le_one₀ hcpos).mpr hc
  have he : c⁻¹ • (c • y - (c - 1) • p) + (1 - c⁻¹) • p = y := by
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ hcpos.ne',
      sub_smul, one_smul]
    module
  have hv := hV.2 (mem_univ (c • y - (c - 1) • p)) (mem_univ p)
    hinv.le (sub_nonneg.mpr hle) (by ring : c⁻¹ + (1 - c⁻¹) = 1)
  rw [he] at hv
  simp only [smul_eq_mul] at hv
  have hh := mul_le_mul_of_nonneg_left (hp y) (sub_nonneg.mpr hle)
  apply (mul_le_mul_iff_right₀ hinv).mp
  linarith

end Submission.Obl.Entropy__smooth_gaussian_transport
