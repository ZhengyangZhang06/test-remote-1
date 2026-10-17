import Submission.Obl.Entropy__affine_exponential_moments.Affine
import Submission.Obl.Entropy__centered_slack_transports.Transport

open MeasureTheory
open Submission.Obl.Entropy__affine_exponential_moments

namespace Submission.Obl.Root.AffineMeasure

/-- The affine density is exactly the pushforward of the original density measure. -/
theorem map_withDensity_affine {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    Measure.map (fun x => e x + b) (volume.withDensity (fun x => ENNReal.ofReal (f x))) =
      volume.withDensity (fun y => ENNReal.ofReal (affineDensity e b f y)) := by
  let T := MeasurableEquiv.addRight b
  have hm := Submission.Obl.Entropy__centered_slack_transports.map_linear_density
    e.toLinearEquiv f
  simp only [ContinuousLinearEquiv.coe_toLinearEquiv] at hm
  change Measure.map (T ∘ e) _ = _
  rw [← Measure.map_map T.measurable e.continuous.measurable, hm,
    Submission.Obl.Entropy__centered_slack_transports.map_withDensity_equiv T]
  have ht : Measure.map T volume = volume := (measurePreserving_add_right volume b).map_eq
  rw [ht]
  congr 1

end Submission.Obl.Root.AffineMeasure
