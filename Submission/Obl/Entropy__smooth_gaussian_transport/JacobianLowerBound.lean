import Submission.Obl.Entropy__smooth_gaussian_transport.AlmostEverywhereEquation

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- The classical Jacobian is a lower bound for the Alexandrov measure even
when the latter may have a singular part. -/
theorem jacobian_measure_le_alexandrov {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hC1 : ContDiff ℝ 1 u)
    (hdom : conjugateDomain u = univ) (hinj : Function.Injective (gradient u)) :
    volume.withDensity (fun x => ENNReal.ofReal |(fderiv ℝ (gradient u) x).det|) ≤
      alexandrovMeasure u := by
  let D : Set (E m) := {x | DifferentiableAt ℝ (gradient u) x}
  have hD : MeasurableSet D := measurableSet_of_differentiableAt ℝ (gradient u)
  have hDae : ∀ᵐ x ∂volume, x ∈ D := ae_differentiable_gradient_convex hu hC1 hdom
  apply Measure.le_iff.mpr
  intro s hs
  have he : (s ∩ D : Set (E m)) =ᵐ[volume] s := by
    filter_upwards [hDae] with x hx
    change (x ∈ s ∧ x ∈ D) = (x ∈ s)
    exact propext ⟨And.left, fun hs => ⟨hs, hx⟩⟩
  rw [withDensity_apply _ hs, ← Measure.restrict_congr_set he]
  calc
    (∫⁻ x in s ∩ D, ENNReal.ofReal |(fderiv ℝ (gradient u) x).det|) =
        volume (gradient u '' (s ∩ D)) :=
      lintegral_abs_det_fderiv_eq_addHaar_image volume (hs.inter hD)
        (fun x hx => hx.2.hasFDerivAt.hasFDerivWithinAt) hinj.injOn
    _ ≤ volume (gradient u '' s) := measure_mono (image_mono inter_subset_left)
    _ = alexandrovMeasure u s := by
      rw [alexandrovMeasure_apply hC1.continuous hdom hs,
        subgradientImage_eq_gradient_image hu hC1.differentiable_one]

theorem density_measure_le_alexandrov_of_ae_le_jacobian {m : ℕ} {u f : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hC1 : ContDiff ℝ 1 u)
    (hdom : conjugateDomain u = univ) (hinj : Function.Injective (gradient u))
    (hf : ∀ᵐ x ∂volume, f x ≤ |(fderiv ℝ (gradient u) x).det|) :
    volume.withDensity (fun x => ENNReal.ofReal (f x)) ≤ alexandrovMeasure u := by
  apply le_trans _ (jacobian_measure_le_alexandrov hu hC1 hdom hinj)
  apply withDensity_mono
  exact hf.mono (fun _ hx => ENNReal.ofReal_le_ofReal hx)

end Submission.Obl.Entropy__smooth_gaussian_transport
