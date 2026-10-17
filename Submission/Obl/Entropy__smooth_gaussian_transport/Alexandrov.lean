import Submission.Obl.Entropy__smooth_gaussian_transport.Subgradient

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- The Monge–Ampère measure, expressed through the conjugate gradient. -/
noncomputable def alexandrovMeasure {m : ℕ} (φ : E m → ℝ) : Measure (E m) :=
  Measure.map (gradient (finiteConjugate φ)) volume

theorem alexandrovMeasure_apply {m : ℕ} {φ : E m → ℝ}
    (hφ : Continuous φ) (hdom : conjugateDomain φ = univ)
    {s : Set (E m)} (hs : MeasurableSet s) :
    alexandrovMeasure φ s = volume (subgradientImage φ s) := by
  rw [alexandrovMeasure, Measure.map_apply
    (Submission.Lib.Brenier.ConvexGradientLaw.measurable_gradient _) hs]
  exact measure_congr (subgradientImage_ae_eq_preimage hφ hdom s).symm

theorem alexandrovMeasure_finiteOnCompacts {m : ℕ} {φ : E m → ℝ}
    (hφ : Continuous φ) (hdom : conjugateDomain φ = univ) :
    IsFiniteMeasureOnCompacts (alexandrovMeasure φ) := by
  constructor
  intro K hK
  rw [alexandrovMeasure_apply hφ hdom hK.measurableSet]
  exact (isCompact_subgradientImage hφ hK).measure_lt_top

/-- Bounds for a density give bounds for its mass on every null-measurable set. -/
theorem withDensity_mass_bounds {m : ℕ} {f : E m → ℝ} (hf : Measurable f)
    {s : Set (E m)} (hs : NullMeasurableSet s volume) {a b : ℝ}
    (hbound : ∀ x ∈ s, a ≤ f x ∧ f x ≤ b) :
    ENNReal.ofReal a * volume s ≤ (volume.withDensity (fun x => ENNReal.ofReal (f x))) s ∧
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) s ≤ ENNReal.ofReal b * volume s := by
  rw [withDensity_apply₀ _ hs]
  constructor
  · calc
      _ = ∫⁻ x in s, ENNReal.ofReal a := (setLIntegral_const _ _).symm
      _ ≤ _ := setLIntegral_mono hf.ennreal_ofReal (fun x hx =>
        ENNReal.ofReal_le_ofReal (hbound x hx).1)
  · calc
      _ ≤ ∫⁻ x in s, ENNReal.ofReal b := setLIntegral_mono measurable_const (fun x hx =>
        ENNReal.ofReal_le_ofReal (hbound x hx).2)
      _ = _ := setLIntegral_const _ _

/-- The Alexandrov measure of the Brenier potential has positive finite density bounds
on every compact set. -/
theorem brenier_alexandrov_bounds {m : ℕ} {V φ : E m → ℝ} (hV : Continuous V)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {K : Set (E m)} (hK : IsCompact K) :
    ∃ l u : ℝ, 0 < l ∧ l ≤ u ∧ ∀ s : Set (E m), MeasurableSet s → s ⊆ K →
      ENNReal.ofReal l * volume s ≤ alexandrovMeasure φ s ∧
        alexandrovMeasure φ s ≤ ENNReal.ofReal u * volume s := by
  have hc := hφ.locallyLipschitz.continuous
  have hdom : conjugateDomain φ = univ := by
    apply conjugateDomain_eq_univ_of_transport hφ (stdGaussian_absolutelyContinuous m)
    rw [hlaw]
    exact target_support hV
  obtain ⟨a, b, ha, hab, habK⟩ := gaussian_density_bounds hK
  obtain ⟨c, d, hcpos, hcd, hcdK⟩ := target_density_bounds hV
    (isCompact_subgradientImage hc hK)
  have hd : 0 < d := hcpos.trans_le hcd
  have hb : 0 < b := ha.trans_le hab
  have hlo : 0 < a / d := div_pos ha hd
  have hlu : a / d ≤ b / c := by
    exact div_le_div₀ hb.le hab hcpos hcd
  refine ⟨a / d, b / c, hlo, hlu, ?_⟩
  intro s hs hsK
  obtain ⟨hμlo, hμhi⟩ := withDensity_mass_bounds
    Submission.Lib.EntropyRemainder.gaussianDensity_continuous.measurable
    hs.nullMeasurableSet (fun x hx => habK x (hsK hx))
  rw [← Submission.Lib.EntropyRemainder.stdGaussian_eq_withDensity] at hμlo hμhi
  obtain ⟨hνlo, hνhi⟩ := withDensity_mass_bounds (f := fun x => Real.exp (-V x))
    (Real.continuous_exp.comp hV.neg).measurable
    (subgradientImage_nullMeasurableSet hc hdom hs)
    (fun y hy => hcdK y (subgradientImage_mono hsK hy))
  rw [brenier_subgradient_mass hV hφ hlaw hs] at hνlo hνhi
  rw [alexandrovMeasure_apply hc hdom hs]
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

theorem map_weighted_law {m : ℕ} {μ : Measure (E m)} {T : E m → E m}
    (hT : Measurable T) {g : E m → ℝ≥0∞} (hg : Measurable g) :
    (Measure.map T μ).withDensity g = Measure.map T (μ.withDensity (fun x => g (T x))) := by
  ext s hs
  rw [withDensity_apply _ hs, Measure.map_apply hT hs, withDensity_apply _ (hT hs),
    setLIntegral_map hs hg hT]

theorem inverse_weighted_law {m : ℕ} {μ : Measure (E m)} {T S : E m → E m}
    (hT : Measurable T) (hS : Measurable S) (hinv : ∀ᵐ x ∂μ, S (T x) = x)
    {g : E m → ℝ≥0∞} (hg : Measurable g) :
    Measure.map S ((Measure.map T μ).withDensity g) =
      μ.withDensity (fun x => g (T x)) := by
  rw [map_weighted_law hT hg, Measure.map_map hS hT]
  change Measure.map (fun x => S (T x)) (μ.withDensity (fun x => g (T x))) = _
  rw [Measure.map_congr ((withDensity_absolutelyContinuous _ _).ae_le hinv)]
  change Measure.map (id : E m → E m) (μ.withDensity (fun x => g (T x))) = _
  exact Measure.map_id

/-- The weighted transport equation gives the full density of the Alexandrov measure. -/
theorem brenier_alexandrov_density {m : ℕ} {V φ : E m → ℝ} (hV : Continuous V)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    alexandrovMeasure φ = volume.withDensity (fun x =>
      ENNReal.ofReal (Submission.Lib.EntropyRemainder.gaussianDensity x *
        Real.exp (V (gradient φ x)))) := by
  have hgm := Submission.Lib.Brenier.ConvexGradientLaw.measurable_gradient φ
  have hgmi := Submission.Lib.Brenier.ConvexGradientLaw.measurable_gradient (finiteConjugate φ)
  have hg : Measurable (fun y => ENNReal.ofReal (Real.exp (V y))) :=
    (Real.continuous_exp.comp hV).measurable.ennreal_ofReal
  have hνinv : (volume.withDensity (fun y => ENNReal.ofReal (Real.exp (-V y)))).withDensity
      (fun y => ENNReal.ofReal (Real.exp (V y))) = volume := by
    rw [← withDensity_mul volume (f := fun y => ENNReal.ofReal (Real.exp (-V y)))
      (Real.continuous_exp.comp hV.neg).measurable.ennreal_ofReal hg]
    convert! (withDensity_one : (volume : Measure (E m)).withDensity 1 = volume) using 1
    congr 1
    ext x
    simp only [Pi.mul_apply, Pi.one_apply, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
      ← Real.exp_add, neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one]
  have h := inverse_weighted_law hgm hgmi (brenier_dual_transport hV hφ hlaw).2.2.2 hg
  rw [hlaw, hνinv] at h
  change alexandrovMeasure φ = _ at h
  rw [h, Submission.Lib.EntropyRemainder.stdGaussian_eq_withDensity,
    ← withDensity_mul volume
      (g := fun x => ENNReal.ofReal (Real.exp (V (gradient φ x))))
      Submission.Lib.EntropyRemainder.gaussianDensity_continuous.measurable.ennreal_ofReal
      (hg.comp hgm)]
  congr 1
  ext x
  exact (ENNReal.ofReal_mul (Submission.Lib.EntropyRemainder.gaussianDensity_pos x).le).symm

theorem brenier_alexandrov_equivalent_volume {m : ℕ} {V φ : E m → ℝ} (hV : Continuous V)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    alexandrovMeasure φ ≪ volume ∧ volume ≪ alexandrovMeasure φ := by
  rw [brenier_alexandrov_density hV hφ hlaw]
  refine ⟨withDensity_absolutelyContinuous _ _, ?_⟩
  apply withDensity_absolutelyContinuous'
  · exact (Submission.Lib.EntropyRemainder.gaussianDensity_continuous.measurable.mul
      ((Real.continuous_exp.comp hV).measurable.comp
        (Submission.Lib.Brenier.ConvexGradientLaw.measurable_gradient φ))).ennreal_ofReal.aemeasurable
  · filter_upwards with x
    exact ENNReal.ofReal_ne_zero_iff.mpr
      (mul_pos (Submission.Lib.EntropyRemainder.gaussianDensity_pos x) (Real.exp_pos _))

end Submission.Obl.Entropy__smooth_gaussian_transport
