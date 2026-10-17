import Submission.Obl.Entropy__affine_exponential_moments.Affine

open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

open Submission.Obl.Entropy__affine_exponential_moments

namespace Submission.Obl.Root.AffineMeasure

/-- A measurable equivalence transports a density by composing it with the inverse. -/
theorem map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (e : α ≃ᵐ β) (f : α → ℝ≥0∞) :
    Measure.map e (μ.withDensity f) = (Measure.map e μ).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [e.map_apply, withDensity_apply f (e.measurable hs),
    withDensity_apply _ hs, e.restrict_map, lintegral_map_equiv]
  simp only [e.symm_apply_apply]

/-- The affine density is exactly the pushforward of the original density measure. -/
theorem map_withDensity_affine {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    Measure.map (fun x => e x + b) (volume.withDensity (fun x => ENNReal.ofReal (f x))) =
      volume.withDensity (fun y => ENNReal.ofReal (affineDensity e b f y)) := by
  let T := e.toHomeomorph.toMeasurableEquiv.trans (MeasurableEquiv.addRight b)
  have hlin : Measure.map e volume =
      ENNReal.ofReal (|LinearMap.det e.toLinearMap|⁻¹) • volume := by
    simpa only [abs_inv, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv] using
      Measure.map_linearMap_addHaar_eq_smul_addHaar volume e.toLinearEquiv.isUnit_det'.ne_zero
  have hmap : Measure.map T volume =
      ENNReal.ofReal (|LinearMap.det e.toLinearMap|⁻¹) • volume := by
    change Measure.map ((fun x => x + b) ∘ e) volume = _
    have ht : Measurable (fun x : EuclideanSpace ℝ (Fin n) => x + b) := by fun_prop
    rw [← Measure.map_map ht e.continuous.measurable,
      hlin, Measure.map_smul, (measurePreserving_add_right volume b).map_eq]
  change Measure.map T (volume.withDensity (fun x => ENNReal.ofReal (f x))) = _
  rw [map_withDensity_equiv, hmap, withDensity_smul_measure,
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  ext y
  simp only [Pi.smul_apply, smul_eq_mul, affineDensity,
    ENNReal.ofReal_mul (inv_nonneg.mpr (abs_nonneg _))]
  rfl

end Submission.Obl.Root.AffineMeasure
