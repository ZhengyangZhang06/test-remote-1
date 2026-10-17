import Mathlib

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Submission.Obl.Entropy__transport_finite_jacobian_energy

/-- The source density of an injective differentiable transport is the pullback
of the target density times the absolute Jacobian. This measure identity does
not require surjectivity. -/
theorem transport_withDensity_pullback
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {T : E → E} {D : E → E →L[ℝ] E}
    (hT : ∀ x, HasFDerivAt T (D x) x) (hinj : Function.Injective T)
    {ρ σ : E → ℝ≥0∞}
    (hmap : (μ.withDensity ρ).map T = μ.withDensity σ) :
    μ.withDensity ρ = μ.withDensity (fun x => ENNReal.ofReal |(D x).det| * σ (T x)) := by
  have hc : Continuous T := continuous_iff_continuousAt.mpr fun x => (hT x).continuousAt
  have he := hc.measurableEmbedding hinj
  apply Measure.ext
  intro s hs
  calc
    μ.withDensity ρ s = (μ.withDensity ρ).map T (T '' s) := by
      rw [he.map_apply, Set.preimage_image_eq _ hinj]
    _ = μ.withDensity σ (T '' s) := by rw [hmap]
    _ = ∫⁻ y in T '' s, σ y ∂μ := withDensity_apply _ (he.measurableSet_image' hs)
    _ = ∫⁻ x in s, ENNReal.ofReal |(D x).det| * σ (T x) ∂μ :=
      lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hs
        (fun x _ => (hT x).hasFDerivWithinAt) hinj.injOn σ
    _ = μ.withDensity (fun x => ENNReal.ofReal |(D x).det| * σ (T x)) s :=
      (withDensity_apply _ hs).symm

/-- For continuous densities and a continuous Jacobian, the transport density
identity holds at every point, not merely almost everywhere. -/
theorem transport_density_pointwise
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {T : E → E} {D : E → E →L[ℝ] E}
    (hT : ∀ x, HasFDerivAt T (D x) x) (hinj : Function.Injective T)
    (hD : Continuous (fun x => (D x).det))
    {ρ σ : E → ℝ} (hρ : Continuous ρ) (hσ : Continuous σ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hσ0 : ∀ x, 0 ≤ σ x)
    (hmap : (μ.withDensity (fun x => ENNReal.ofReal (ρ x))).map T =
      μ.withDensity (fun x => ENNReal.ofReal (σ x))) (x : E) :
    ρ x = |(D x).det| * σ (T x) := by
  have hc : Continuous T := continuous_iff_continuousAt.mpr fun x => (hT x).continuousAt
  have hrhs : Continuous (fun x => |(D x).det| * σ (T x)) := hD.abs.mul (hσ.comp hc)
  have hm := transport_withDensity_pullback μ hT hinj hmap
  simp_rw [← ENNReal.ofReal_mul (abs_nonneg _)] at hm
  have hae := (withDensity_eq_iff_of_sigmaFinite
    hρ.measurable.ennreal_ofReal.aemeasurable hrhs.measurable.ennreal_ofReal.aemeasurable).mp hm
  have hae' : ρ =ᵐ[μ] (fun x => |(D x).det| * σ (T x)) := by
    filter_upwards [hae] with y hy
    exact (ENNReal.ofReal_eq_ofReal_iff (hρ0 y)
      (mul_nonneg (abs_nonneg _) (hσ0 _))).mp hy
  exact congrFun (Measure.eq_of_ae_eq hae' hρ hrhs) x

/-- Taking logarithms of the continuous transport density identity. -/
theorem transport_logdet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {T : E → E} {D : E → E →L[ℝ] E}
    (hT : ∀ x, HasFDerivAt T (D x) x) (hinj : Function.Injective T)
    (hD : Continuous (fun x => (D x).det)) (hpos : ∀ x, 0 < (D x).det)
    {U V : E → ℝ} (hU : Continuous U) (hV : Continuous V)
    (hmap : (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-U x)))).map T =
      μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) (x : E) :
    Real.log (D x).det = V (T x) - U x := by
  have he := transport_density_pointwise μ hT hinj hD (Real.continuous_exp.comp hU.neg) (Real.continuous_exp.comp hV.neg)
    (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le) hmap x
  rw [abs_of_pos (hpos x)] at he
  have hl := congrArg Real.log he
  dsimp only [Function.comp_def, Pi.neg_apply] at hl
  rw [Real.log_exp, Real.log_mul (ne_of_gt (hpos x)) (Real.exp_ne_zero _),
    Real.log_exp] at hl
  linarith

end Submission.Obl.Entropy__transport_finite_jacobian_energy
