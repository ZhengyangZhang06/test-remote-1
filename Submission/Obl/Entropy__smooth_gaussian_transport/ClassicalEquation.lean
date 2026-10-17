import Submission.Obl.Entropy__smooth_gaussian_transport.DifferentiableTransport

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem subgradientImage_eq_gradient_image {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hd : Differentiable ℝ u) (s : Set (E m)) :
    subgradientImage u s = gradient u '' s := by
  ext p
  constructor
  · rintro ⟨x, hx, hp⟩
    exact ⟨x, hx, Submission.Lib.Brenier.ConvexGradientLaw.gradient_eq_of_support (hd x) hp⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, convex_gradient_support hu (hd x)⟩

/-- Once the gradient is differentiable and injective, the Alexandrov measure
is its classical Jacobian measure. -/
theorem alexandrovMeasure_eq_withDensity_abs_det {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ)
    (hd : Differentiable ℝ u) (hg : Differentiable ℝ (gradient u))
    (hinj : Function.Injective (gradient u)) :
    alexandrovMeasure u = volume.withDensity
      (fun x => ENNReal.ofReal |(fderiv ℝ (gradient u) x).det|) := by
  ext s hs
  rw [alexandrovMeasure_apply hd.continuous hdom hs,
    subgradientImage_eq_gradient_image hu hd, withDensity_apply _ hs]
  exact (lintegral_abs_det_fderiv_eq_addHaar_image volume hs
    (fun x _ => (hg x).hasFDerivAt.hasFDerivWithinAt) hinj.injOn).symm

theorem contDiff_one_gradient_of_contDiff_two {m : ℕ} {u : E m → ℝ}
    (hu : ContDiff ℝ 2 u) : ContDiff ℝ 1 (gradient u) := by
  exact (InnerProductSpace.toDual ℝ (E m)).symm.toContinuousLinearMap.contDiff.comp
    (hu.fderiv_right (by norm_num))

/-- With C² regularity, equality of the Alexandrov measures implies equality
of the continuous Jacobian densities at every point. -/
theorem abs_det_fderiv_gradient_eq_density {m : ℕ} {u f : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ)
    (hC2 : ContDiff ℝ 2 u) (hinj : Function.Injective (gradient u))
    (hf : Continuous f) (hfnonneg : ∀ x, 0 ≤ f x)
    (hMA : alexandrovMeasure u = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (x : E m) : |(fderiv ℝ (gradient u) x).det| = f x := by
  have hg := contDiff_one_gradient_of_contDiff_two hC2
  have hc : Continuous (fun x => |(fderiv ℝ (gradient u) x).det|) :=
    (ContinuousLinearMap.continuous_det.comp (hg.continuous_fderiv (by norm_num))).abs
  have hmeasures : volume.withDensity (fun x => ENNReal.ofReal |(fderiv ℝ (gradient u) x).det|) =
      volume.withDensity (fun x => ENNReal.ofReal (f x)) :=
    (alexandrovMeasure_eq_withDensity_abs_det hu hdom
      (hC2.differentiable (by norm_num)) hg.differentiable_one hinj).symm.trans hMA
  have hae := (withDensity_eq_iff_of_sigmaFinite hc.measurable.ennreal_ofReal.aemeasurable
    hf.measurable.ennreal_ofReal.aemeasurable).mp hmeasures
  have haereal : (fun x => |(fderiv ℝ (gradient u) x).det|) =ᵐ[volume] f := by
    filter_upwards [hae] with y hy
    exact (ENNReal.ofReal_eq_ofReal_iff (abs_nonneg _) (hfnonneg y)).mp hy
  exact congr_fun (Measure.eq_of_ae_eq haereal hc hf) x

/-- The transport equation is classical as soon as the Brenier potential is C². -/
theorem brenier_classical_density_of_contDiff_two {m : ℕ} (hm : 1 ≤ m) {V φ : E m → ℝ}
    (hV : Continuous V) (hφ : ConvexOn ℝ univ φ) (hC2 : ContDiff ℝ 2 φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) (x : E m) :
    |(fderiv ℝ (gradient φ) x).det| =
      Submission.Lib.EntropyRemainder.gaussianDensity x * Real.exp (V (gradient φ x)) := by
  have hdom : conjugateDomain φ = univ := by
    apply conjugateDomain_eq_univ_of_transport hφ (stdGaussian_absolutelyContinuous m)
    rw [hlaw]
    exact target_support hV
  exact abs_det_fderiv_gradient_eq_density hφ hdom hC2
    (brenierGradientHomeomorph hm hV hφ hlaw).injective
    (brenier_alexandrov_continuous_density hm hV hφ hlaw)
    (fun y => mul_nonneg (Submission.Lib.EntropyRemainder.gaussianDensity_pos y).le
      (Real.exp_pos _).le) (brenier_alexandrov_density hV hφ hlaw) x

theorem brenier_det_fderiv_gradient_ne_zero_of_contDiff_two {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} (hV : Continuous V) (hφ : ConvexOn ℝ univ φ)
    (hC2 : ContDiff ℝ 2 φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) (x : E m) :
    (fderiv ℝ (gradient φ) x).det ≠ 0 := by
  apply abs_pos.mp
  rw [brenier_classical_density_of_contDiff_two hm hV hφ hC2 hlaw x]
  exact mul_pos (Submission.Lib.EntropyRemainder.gaussianDensity_pos x) (Real.exp_pos _)

end Submission.Obl.Entropy__smooth_gaussian_transport
