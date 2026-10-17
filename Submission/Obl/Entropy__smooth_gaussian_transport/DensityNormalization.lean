import Submission.Obl.Entropy__smooth_gaussian_transport.DepthEstimate

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

def LocalDensityBounds {m : ℕ} (u : E m → ℝ) : Prop :=
  ∀ K : Set (E m), IsCompact K → ∃ l U : ℝ, 0 < l ∧ l ≤ U ∧
    ∀ s : Set (E m), MeasurableSet s → s ⊆ K →
      ENNReal.ofReal l * volume s ≤ alexandrovMeasure u s ∧
        alexandrovMeasure u s ≤ ENNReal.ofReal U * volume s

theorem localDensityBounds_tilt {m : ℕ} {u : E m → ℝ} (hu : Continuous u)
    (hdom : conjugateDomain u = univ) (hb : LocalDensityBounds u) (p : E m) (r : ℝ) :
    LocalDensityBounds (tilt u p r) := by
  intro K hK
  simpa only [tilt_alexandrovMeasure hu hdom p r] using hb K hK

theorem localDensityBounds_translate {m : ℕ} {u : E m → ℝ} (hu : Continuous u)
    (hdom : conjugateDomain u = univ) (hb : LocalDensityBounds u) (c : E m) :
    LocalDensityBounds (fun z => u (z + c)) := by
  intro K hK
  obtain ⟨l, U, hl, hlU, hbound⟩ := hb ((fun z => z + c) '' K)
    (hK.image (continuous_id.add continuous_const))
  refine ⟨l, U, hl, hlU, ?_⟩
  intro s hs hsK
  have hs' : MeasurableSet ((fun z => z + c) '' s) :=
    (Homeomorph.addRight c).measurableEmbedding.measurableSet_image.mpr hs
  have hvol : volume ((fun z => z + c) '' s) = volume s := by
    rw [image_add_right, measure_preimage_add_right]
  rw [translate_alexandrov hu hdom c hs]
  simpa only [hvol] using hbound _ hs' (image_mono hsK)

/-- After an arbitrary invertible linear change, a positive rescaling of the
potential fixes the lower density at two and preserves the upper/lower ratio. -/
theorem exists_density_normalizing_scale {m : ℕ} (hm : 1 ≤ m) {u : E m → ℝ}
    (hu : Continuous u) (hdom : conjugateDomain u = univ) (L : E m ≃L[ℝ] E m)
    {K : Set (E m)} {l U : ℝ} (hl : 0 < l) (hlU : l ≤ U)
    (hb : ∀ s : Set (E m), MeasurableSet s → s ⊆ K →
      ENNReal.ofReal l * volume s ≤ alexandrovMeasure u s ∧
        alexandrovMeasure u s ≤ ENNReal.ofReal U * volume s) :
    ∃ a : ℝ, 0 < a ∧ ∀ s : Set (E m), MeasurableSet s → s ⊆ L ⁻¹' K →
      (2 : ℝ≥0∞) * volume s ≤ alexandrovMeasure (fun x => a * u (L x)) s ∧
        alexandrovMeasure (fun x => a * u (L x)) s ≤ ENNReal.ofReal (2 * U / l) * volume s := by
  let D : ℝ := |L.toLinearMap.det|
  have hD : 0 < D := abs_pos.mpr L.toLinearEquiv.isUnit_det'.ne_zero
  let a : ℝ := (2 / (l * D ^ 2)) ^ ((m : ℝ)⁻¹)
  have ha : 0 < a := Real.rpow_pos_of_pos (by positivity) _
  have haeq : a ^ m = 2 / (l * D ^ 2) :=
    Real.rpow_inv_natCast_pow (by positivity) (by omega)
  have hlo : a ^ m * (l * D ^ 2) = 2 := by rw [haeq]; field_simp
  have hhi : a ^ m * (U * D ^ 2) = 2 * U / l := by rw [haeq]; field_simp
  refine ⟨a, ha, ?_⟩
  intro s hs hsK
  obtain ⟨hlo', hhi'⟩ := linearChange_mass_bounds hu hdom L hl.le (hl.le.trans hlU) hb hs hsK
  have hscale : alexandrovMeasure (fun x => a * u (L x)) s =
      ENNReal.ofReal (a ^ m) * alexandrovMeasure (u ∘ L) s := by
    exact positiveScale_alexandrov (hu.comp L.continuous) (linearChange_conjugateDomain hdom L) ha hs
  rw [hscale]
  have hloprod := mul_le_mul_right hlo' (ENNReal.ofReal (a ^ m))
  have hhiprod := mul_le_mul_right hhi' (ENNReal.ofReal (a ^ m))
  have hlow : ENNReal.ofReal (a ^ m) * ENNReal.ofReal (l * D ^ 2) = 2 := by
    rw [← ENNReal.ofReal_mul (pow_nonneg ha.le m), hlo]
    norm_num
  have hupp : ENNReal.ofReal (a ^ m) * ENNReal.ofReal (U * D ^ 2) =
      ENNReal.ofReal (2 * U / l) := by
    rw [← ENNReal.ofReal_mul (pow_nonneg ha.le m), hhi]
  dsimp only [D] at hlow hupp
  constructor
  · simpa only [← mul_assoc, hlow] using hloprod
  · simpa only [← mul_assoc, hupp] using hhiprod

end Submission.Obl.Entropy__smooth_gaussian_transport
