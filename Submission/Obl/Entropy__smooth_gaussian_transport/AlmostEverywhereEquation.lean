import Submission.Obl.Entropy__smooth_gaussian_transport.AlmostEverywhereHessian
import Submission.Obl.Entropy__smooth_gaussian_transport.ClassicalEquation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- For a C¹ convex potential with injective gradient and absolutely continuous
Alexandrov measure, the Jacobian formula needs only the almost-everywhere
second differentiability supplied by the convexity theorem. -/
theorem alexandrov_eq_jacobian_of_absolutelyContinuous {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hC1 : ContDiff ℝ 1 u) (hdom : conjugateDomain u = univ)
    (hinj : Function.Injective (gradient u)) (hac : alexandrovMeasure u ≪ volume) :
    alexandrovMeasure u = volume.withDensity
      (fun x => ENNReal.ofReal |(fderiv ℝ (gradient u) x).det|) := by
  let D : Set (E m) := {x | DifferentiableAt ℝ (gradient u) x}
  have hD : MeasurableSet D := measurableSet_of_differentiableAt ℝ (gradient u)
  have hDae : ∀ᵐ x ∂volume, x ∈ D := ae_differentiable_gradient_convex hu hC1 hdom
  ext s hs
  have hsu : (s ∩ D : Set (E m)) =ᵐ[alexandrovMeasure u] s := by
    filter_upwards [hac.ae_le hDae] with x hx
    change (x ∈ s ∧ x ∈ D) = (x ∈ s)
    exact propext ⟨And.left, fun hs => ⟨hs, hx⟩⟩
  have hsv : (s ∩ D : Set (E m)) =ᵐ[volume] s := by
    filter_upwards [hDae] with x hx
    change (x ∈ s ∧ x ∈ D) = (x ∈ s)
    exact propext ⟨And.left, fun hs => ⟨hs, hx⟩⟩
  calc
    alexandrovMeasure u s = alexandrovMeasure u (s ∩ D) := (measure_congr hsu).symm
    _ = volume (gradient u '' (s ∩ D)) := by
      rw [alexandrovMeasure_apply hC1.continuous hdom (hs.inter hD),
        subgradientImage_eq_gradient_image hu hC1.differentiable_one]
    _ = ∫⁻ x in s ∩ D, ENNReal.ofReal |(fderiv ℝ (gradient u) x).det| :=
      (lintegral_abs_det_fderiv_eq_addHaar_image volume (hs.inter hD)
        (fun x hx => hx.2.hasFDerivAt.hasFDerivWithinAt) hinj.injOn).symm
    _ = ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ (gradient u) x).det| := by
      rw [Measure.restrict_congr_set hsv]
    _ = (volume.withDensity (fun x => ENNReal.ofReal |(fderiv ℝ (gradient u) x).det|)) s :=
      (withDensity_apply _ hs).symm

theorem ae_abs_det_fderiv_gradient_eq_density {m : ℕ} {u f : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hC1 : ContDiff ℝ 1 u) (hdom : conjugateDomain u = univ)
    (hinj : Function.Injective (gradient u)) (hf : Measurable f) (hfpos : ∀ x, 0 ≤ f x)
    (hMA : alexandrovMeasure u = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    ∀ᵐ x ∂volume, |(fderiv ℝ (gradient u) x).det| = f x := by
  have hac : alexandrovMeasure u ≪ volume := by
    rw [hMA]
    exact withDensity_absolutelyContinuous _ _
  have hj := alexandrov_eq_jacobian_of_absolutelyContinuous hu hC1 hdom hinj hac
  have hmeas : Measurable (fun x => |(fderiv ℝ (gradient u) x).det|) :=
    (ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ (gradient u))).abs
  have hae := (withDensity_eq_iff_of_sigmaFinite hmeas.ennreal_ofReal.aemeasurable
    hf.ennreal_ofReal.aemeasurable).mp (hj.symm.trans hMA)
  filter_upwards [hae] with x hx
  exact (ENNReal.ofReal_eq_ofReal_iff (abs_nonneg _) (hfpos x)).mp hx

/-- The exact Monge–Ampère equation holds at almost every point without
assuming C² regularity. -/
theorem brenier_ae_classical_density {m : ℕ} (hm : 1 ≤ m) {V φ : E m → ℝ}
    (hV : Continuous V) (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    ∀ᵐ x ∂volume, DifferentiableAt ℝ (gradient φ) x ∧
      |(fderiv ℝ (gradient φ) x).det| =
        Submission.Lib.EntropyRemainder.gaussianDensity x * Real.exp (V (gradient φ x)) := by
  have hdom : conjugateDomain φ = univ := by
    apply conjugateDomain_eq_univ_of_transport hφ (stdGaussian_absolutelyContinuous m)
    rw [hlaw]
    exact target_support hV
  have hC1 := (brenier_contDiff_one hm hV hφ hlaw).1
  have hf := (brenier_alexandrov_continuous_density hm hV hφ hlaw).measurable
  have hnonneg (x : E m) :
      0 ≤ Submission.Lib.EntropyRemainder.gaussianDensity x * Real.exp (V (gradient φ x)) := by
    exact mul_nonneg (Submission.Lib.EntropyRemainder.gaussianDensity_pos x).le (Real.exp_pos _).le
  exact (ae_differentiable_gradient_convex hφ hC1 hdom).and
    (ae_abs_det_fderiv_gradient_eq_density hφ hC1 hdom
      (brenierGradientHomeomorph hm hV hφ hlaw).injective hf hnonneg
      (brenier_alexandrov_density hV hφ hlaw))

end Submission.Obl.Entropy__smooth_gaussian_transport
