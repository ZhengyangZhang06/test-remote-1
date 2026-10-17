import Mathlib

/-!
The survival-function integration step in Lemma 2.1 of the supplied paper.
Submultiplicativity bounds the first moment of a nonnegative function by the
square of its mass. Tonelli is encapsulated by the layer-cake formula.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace Submission.Obl.Root.Survival

/-- Translate a tail integral to the positive half-line. -/
theorem lintegral_tail_eq_translate (S : ℝ → ℝ≥0∞) (hS : Measurable S) (t : ℝ) :
    (∫⁻ x in Ioi t, S x) = ∫⁻ u in Ioi (0 : ℝ), S (t + u) := by
  have h := (measurePreserving_add_left (volume : Measure ℝ) t).setLIntegral_comp_preimage
    (s := Ioi t) measurableSet_Ioi hS
  have hp : (fun x : ℝ => t + x) ⁻¹' Ioi t = Ioi 0 := by
    ext x
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro hx <;> linarith
  rw [hp] at h
  exact h.symm

/-- Integration of a submultiplicative survival function, allowing infinite values. -/
theorem lintegral_mul_le_sq (S : ℝ → ℝ≥0∞) (hS : Measurable S)
    (hsub : ∀ u > 0, ∀ v > 0, S (u + v) ≤ S u * S v) :
    (∫⁻ x in Ioi (0 : ℝ), S x * ENNReal.ofReal x) ≤
      (∫⁻ x in Ioi (0 : ℝ), S x) ^ 2 := by
  let μ := (volume.restrict (Ioi (0 : ℝ))).withDensity S
  have hpos : 0 ≤ᵐ[μ] (fun x : ℝ => x) := by
    change ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))).withDensity S, 0 ≤ x
    rw [ae_withDensity_iff hS]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact fun _ => hx.le
  have htail (t : ℝ) (ht : 0 < t) : μ (Ioi t) = ∫⁻ u in Ioi (0 : ℝ), S (t + u) := by
    dsimp [μ]
    rw [withDensity_apply S measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_left.mpr (Ioi_subset_Ioi ht.le)]
    exact lintegral_tail_eq_translate S hS t
  calc
    (∫⁻ x in Ioi (0 : ℝ), S x * ENNReal.ofReal x) =
        ∫⁻ x, ENNReal.ofReal x ∂μ :=
      (lintegral_withDensity_eq_lintegral_mul _ hS ENNReal.measurable_ofReal).symm
    _ = ∫⁻ t in Ioi (0 : ℝ), μ (Ioi t) :=
      lintegral_eq_lintegral_meas_lt μ hpos measurable_id.aemeasurable
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), S t * (∫⁻ u in Ioi (0 : ℝ), S u) := by
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      rw [htail t ht, ← lintegral_const_mul _ hS]
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
      exact hsub t ht u hu
    _ = (∫⁻ x in Ioi (0 : ℝ), S x) ^ 2 := by
      rw [lintegral_mul_const _ hS, pow_two]

/-- A finite integral of a nonnegative submultiplicative function gives a finite first moment. -/
theorem integrable_mul (S : ℝ → ℝ) (hS : Measurable S)
    (h0 : ∀ x > 0, 0 ≤ S x) (hI : IntegrableOn S (Ioi 0))
    (hsub : ∀ u > 0, ∀ v > 0, S (u + v) ≤ S u * S v) :
    IntegrableOn (fun x => x * S x) (Ioi 0) := by
  have hbound := lintegral_mul_le_sq (fun x => ENNReal.ofReal (S x)) hS.ennreal_ofReal
    (fun u hu v hv => by
      simpa only [ENNReal.ofReal_mul (h0 u hu)] using ENNReal.ofReal_le_ofReal (hsub u hu v hv))
  have heq : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x * S x)) =
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (S x) * ENNReal.ofReal x := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    rw [ENNReal.ofReal_mul hx.le, mul_comm]
  refine ⟨(measurable_id.mul hS).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal ?_).mpr
  · rw [heq]
    exact lt_of_le_of_lt hbound (ENNReal.pow_lt_top hI.lintegral_lt_top)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact mul_nonneg hx.le (h0 x hx)

/-- The real-valued survival estimate used in the Gaussian excess-variance bound. -/
theorem integral_mul_le_sq (S : ℝ → ℝ) (hS : Measurable S)
    (h0 : ∀ x > 0, 0 ≤ S x) (hI : IntegrableOn S (Ioi 0))
    (hsub : ∀ u > 0, ∀ v > 0, S (u + v) ≤ S u * S v) :
    (∫ x in Ioi (0 : ℝ), x * S x) ≤ (∫ x in Ioi (0 : ℝ), S x) ^ 2 := by
  have hbound := lintegral_mul_le_sq (fun x => ENNReal.ofReal (S x)) hS.ennreal_ofReal
    (fun u hu v hv => by
      simpa only [ENNReal.ofReal_mul (h0 u hu)] using ENNReal.ofReal_le_ofReal (hsub u hu v hv))
  have h0ae : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] S := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx using h0 x hx
  have hw0 : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun x => x * S x) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact mul_nonneg hx.le (h0 x hx)
  have hw := integrable_mul S hS h0 hI hsub
  have heq : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (S x) * ENNReal.ofReal x) =
      ENNReal.ofReal (∫ x in Ioi (0 : ℝ), x * S x) := by
    rw [ofReal_integral_eq_lintegral_ofReal hw hw0]
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    rw [ENNReal.ofReal_mul hx.le, mul_comm]
  rw [heq, ← ofReal_integral_eq_lintegral_ofReal hI h0ae, ← ENNReal.ofReal_pow
    (integral_nonneg_of_ae h0ae)] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp hbound

/-- The survival estimate gives the second-moment bound in Lemma 2.1. -/
theorem lintegral_half_sq_le_sq_mean (μ : Measure ℝ)
    (h0 : ∀ᵐ x ∂μ, 0 ≤ x)
    (hsub : ∀ u > 0, ∀ v > 0, μ (Ioi (u + v)) ≤ μ (Ioi u) * μ (Ioi v)) :
    (∫⁻ x, ENNReal.ofReal (x ^ 2 / 2) ∂μ) ≤ (∫⁻ x, ENNReal.ofReal x ∂μ) ^ 2 := by
  have hS : Measurable (fun t : ℝ => μ (Ioi t)) :=
    (show Antitone (fun t : ℝ => μ (Ioi t)) from
      fun _ _ hab => measure_mono (Ioi_subset_Ioi hab)).measurable
  have h := lintegral_comp_eq_lintegral_meas_lt_mul (f := fun x : ℝ => x)
    (g := fun t : ℝ => t) μ h0 measurable_id.aemeasurable
    (fun t _ => continuous_id.intervalIntegrable 0 t) (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht using ht.le)
  simp only [integral_id, zero_pow (by decide : 2 ≠ 0), sub_zero] at h
  rw [h, lintegral_eq_lintegral_meas_lt μ h0 measurable_id.aemeasurable]
  exact lintegral_mul_le_sq _ hS hsub

/-- A nonnegative law with submultiplicative survival and a finite mean has a finite second moment. -/
theorem integrable_sq (μ : Measure ℝ) (h0 : ∀ᵐ x ∂μ, 0 ≤ x)
    (hI : Integrable (fun x : ℝ => x) μ)
    (hsub : ∀ u > 0, ∀ v > 0, μ (Ioi (u + v)) ≤ μ (Ioi u) * μ (Ioi v)) :
    Integrable (fun x : ℝ => x ^ 2) μ := by
  have hbound := lintegral_half_sq_le_sq_mean μ h0 hsub
  have hh : Integrable (fun x : ℝ => x ^ 2 / 2) μ := by
    refine ⟨(by fun_prop), (hasFiniteIntegral_iff_ofReal ?_).mpr ?_⟩
    · exact Eventually.of_forall (fun x => div_nonneg (sq_nonneg x) (by norm_num))
    · exact lt_of_le_of_lt hbound (ENNReal.pow_lt_top hI.lintegral_lt_top)
  convert hh.const_mul 2 using 1
  ext x
  ring

/-- The second moment is at most twice the square of the first moment. -/
theorem integral_sq_le_two_mul_sq_mean (μ : Measure ℝ) (h0 : ∀ᵐ x ∂μ, 0 ≤ x)
    (hI : Integrable (fun x : ℝ => x) μ)
    (hsub : ∀ u > 0, ∀ v > 0, μ (Ioi (u + v)) ≤ μ (Ioi u) * μ (Ioi v)) :
    (∫ x, x ^ 2 ∂μ) ≤ 2 * (∫ x, x ∂μ) ^ 2 := by
  have hbound := lintegral_half_sq_le_sq_mean μ h0 hsub
  have hI2 := integrable_sq μ h0 hI hsub
  have hh0 : 0 ≤ᵐ[μ] (fun x : ℝ => x ^ 2 / 2) :=
    Eventually.of_forall (fun x => div_nonneg (sq_nonneg x) (by norm_num))
  rw [← ofReal_integral_eq_lintegral_ofReal (hI2.div_const 2) hh0,
    ← ofReal_integral_eq_lintegral_ofReal hI h0,
    ← ENNReal.ofReal_pow (integral_nonneg_of_ae h0), integral_div] at hbound
  have hb := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp hbound
  linarith

/-- For a probability law the second-moment estimate is the variance bound used in Lemma 2.1. -/
theorem variance_le_sq_mean (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h0 : ∀ᵐ x ∂μ, 0 ≤ x) (hI : Integrable (fun x : ℝ => x) μ)
    (hsub : ∀ u > 0, ∀ v > 0, μ (Ioi (u + v)) ≤ μ (Ioi u) * μ (Ioi v)) :
    ProbabilityTheory.variance (fun x : ℝ => x) μ ≤ (∫ x, x ∂μ) ^ 2 := by
  have hI2 : MemLp (fun x : ℝ => x) 2 μ :=
    (memLp_two_iff_integrable_sq hI.aestronglyMeasurable).mpr (integrable_sq μ h0 hI hsub)
  rw [ProbabilityTheory.variance_eq_sub hI2]
  have h := integral_sq_le_two_mul_sq_mean μ h0 hI hsub
  change (∫ x, x ^ 2 ∂μ) - (∫ x, x ∂μ) ^ 2 ≤ (∫ x, x ∂μ) ^ 2
  linarith

/-- Log concavity of a positive survival function normalized at zero implies submultiplicativity. -/
theorem submultiplicative_of_log_concave (S : ℝ → ℝ)
    (hpos : ∀ x ∈ Ici (0 : ℝ), 0 < S x) (hzero : S 0 = 1)
    (hlog : ConcaveOn ℝ (Ici (0 : ℝ)) (fun x => Real.log (S x))) :
    ∀ u > 0, ∀ v > 0, S (u + v) ≤ S u * S v := by
  intro u hu v hv
  have hsum : 0 < u + v := add_pos hu hv
  have hs : u / (u + v) + v / (u + v) = 1 := by
    rw [← add_div, div_self hsum.ne']
  have hs' : v / (u + v) + u / (u + v) = 1 := by linarith
  have hh0 : (0 : ℝ) ∈ Ici 0 := by simp
  have hh1 : u + v ∈ Ici (0 : ℝ) := hsum.le
  have h₁ := hlog.2 hh1 hh0 (div_nonneg hu.le hsum.le) (div_nonneg hv.le hsum.le) hs
  have h₂ := hlog.2 hh1 hh0 (div_nonneg hv.le hsum.le) (div_nonneg hu.le hsum.le) hs'
  simp only [smul_eq_mul, mul_zero, add_zero, div_mul_cancel₀ _ hsum.ne',
    hzero, Real.log_one] at h₁ h₂
  have hlogs : Real.log (S (u + v)) ≤ Real.log (S u) + Real.log (S v) := by
    have hsumlog := congrArg (fun r : ℝ => r * Real.log (S (u + v))) hs
    simp only [add_mul, one_mul] at hsumlog
    linarith
  rw [← Real.log_mul (hpos u hu.le).ne' (hpos v hv.le).ne'] at hlogs
  exact (Real.log_le_log_iff (hpos (u + v) hsum.le)
    (mul_pos (hpos u hu.le) (hpos v hv.le))).mp hlogs

end Submission.Obl.Root.Survival
