import Submission.Obl.Entropy__smooth_gaussian_transport.StrictConvexity

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- The reverse transport also has locally positive bounded Alexandrov density. -/
theorem brenier_dual_alexandrov_bounds {m : ℕ} {V φ : E m → ℝ} (hV : Continuous V)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    LocalDensityBounds (finiteConjugate φ) := by
  have hdom : conjugateDomain φ = univ := by
    apply conjugateDomain_eq_univ_of_transport hφ (stdGaussian_absolutelyContinuous m)
    rw [hlaw]
    exact target_support hV
  have hψ := finiteConjugate_convex hdom
  have hc := hψ.locallyLipschitz.continuous
  have hψdom := conjugateDomain_finiteConjugate hdom
  have hlaw' : Measure.map (gradient (finiteConjugate (finiteConjugate φ)))
      (stdGaussian (E m)) = volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))) := by
    rwa [finiteConjugate_involutive hφ hdom]
  intro K hK
  obtain ⟨a, b, ha, hab, habK⟩ := target_density_bounds hV hK
  obtain ⟨c, d, hcpos, hcd, hcdK⟩ := gaussian_density_bounds
    (isCompact_subgradientImage hc hK)
  have hd : 0 < d := hcpos.trans_le hcd
  have hb : 0 < b := ha.trans_le hab
  have hlo : 0 < a / d := div_pos ha hd
  have hlu : a / d ≤ b / c := div_le_div₀ hb.le hab hcpos hcd
  refine ⟨a / d, b / c, hlo, hlu, ?_⟩
  intro s hs hsK
  obtain ⟨hμlo, hμhi⟩ := withDensity_mass_bounds (f := fun x => Real.exp (-V x))
    (Real.continuous_exp.comp hV.neg).measurable
    hs.nullMeasurableSet (fun x hx => habK x (hsK hx))
  obtain ⟨hνlo, hνhi⟩ := withDensity_mass_bounds
    Submission.Lib.EntropyRemainder.gaussianDensity_continuous.measurable
    (subgradientImage_nullMeasurableSet hc hψdom hs)
    (fun y hy => hcdK y (subgradientImage_mono hsK hy))
  rw [← Submission.Lib.EntropyRemainder.stdGaussian_eq_withDensity,
    measure_subgradientImage hc hψdom (stdGaussian_absolutelyContinuous m) hlaw' hs] at hνlo hνhi
  rw [alexandrovMeasure_apply hc hψdom hs]
  constructor
  · rw [ENNReal.ofReal_div_of_pos hd, div_eq_mul_inv, mul_right_comm,
      ← div_eq_mul_inv]
    apply (ENNReal.div_le_iff' (ENNReal.ofReal_ne_zero_iff.mpr hd) ENNReal.ofReal_ne_top).mpr
    exact hμlo.trans hνhi
  · rw [ENNReal.ofReal_div_of_pos hcpos, div_eq_mul_inv, mul_right_comm,
      ← div_eq_mul_inv]
    apply (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr hcpos))
      (Or.inl ENNReal.ofReal_ne_top)).mpr
    rw [mul_comm]
    exact hνlo.trans hμhi

theorem brenier_strictConvexOn {m : ℕ} (hm : 1 ≤ m) {V φ : E m → ℝ}
    (hV : Continuous V) (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    StrictConvexOn ℝ univ φ ∧ StrictConvexOn ℝ univ (finiteConjugate φ) := by
  have hdom : conjugateDomain φ = univ := by
    apply conjugateDomain_eq_univ_of_transport hφ (stdGaussian_absolutelyContinuous m)
    rw [hlaw]
    exact target_support hV
  exact ⟨strictConvexOn_of_localDensityBounds hm hφ hdom
    (fun _ hK => brenier_alexandrov_bounds hV hφ hlaw hK),
    strictConvexOn_of_localDensityBounds hm (finiteConjugate_convex hdom)
      (conjugateDomain_finiteConjugate hdom) (brenier_dual_alexandrov_bounds hV hφ hlaw)⟩

end Submission.Obl.Entropy__smooth_gaussian_transport
