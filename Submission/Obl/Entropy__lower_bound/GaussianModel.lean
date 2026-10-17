import Mathlib

/-! Basic calculus for the scalar Gaussian parametrization in Section 2.1. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff

namespace Submission.Obl.Entropy__lower_bound

/-- The standard normal density. -/
noncomputable def normalPDF : ℝ → ℝ := gaussianPDFReal 0 1

/-- The standard normal distribution function. -/
noncomputable def normalCDF : ℝ → ℝ := cdf (gaussianReal 0 1)

/-- The Gaussian-to-exponential scalar transport. -/
noncomputable def exponentialTransport (a : ℝ) : ℝ := -Real.log (normalCDF (-a))

/-- The positive derivative of the scalar transport. -/
noncomputable def gaussianHazard (a : ℝ) : ℝ := normalPDF a / normalCDF (-a)

/-- The normal density is positive everywhere. -/
theorem normalPDF_pos (a : ℝ) : 0 < normalPDF a :=
  gaussianPDFReal_pos 0 1 a one_ne_zero

/-- The normal density is even. -/
theorem normalPDF_neg (a : ℝ) : normalPDF (-a) = normalPDF a := by
  simp [normalPDF, gaussianPDFReal]

/-- Smoothness of the standard normal density. -/
theorem contDiff_normalPDF : ContDiff ℝ ∞ normalPDF := by
  unfold normalPDF gaussianPDFReal
  fun_prop

/-- The library's probabilistic CDF agrees with the integral of the density. -/
theorem normalCDF_eq_integral (a : ℝ) : normalCDF a = ∫ x in Iic a, normalPDF x := by
  rw [normalCDF, cdf_eq_real, Measure.real,
    gaussianReal_apply_eq_integral 0 one_ne_zero]
  exact ENNReal.toReal_ofReal (integral_nonneg (fun x => (normalPDF_pos x).le))

/-- Every finite threshold has positive probability to its left. -/
theorem normalCDF_pos (a : ℝ) : 0 < normalCDF a := by
  rw [normalCDF_eq_integral]
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (fun x => (normalPDF_pos x).le))
    (integrable_gaussianPDFReal 0 1).integrableOn).2
  have hs : Function.support normalPDF = univ := by
    ext x
    simp [Function.mem_support, ne_of_gt (normalPDF_pos x)]
  rw [hs, univ_inter, Real.volume_Iic]
  exact ENNReal.zero_lt_top

/-- The CDF has derivative equal to the density. -/
theorem hasDerivAt_normalCDF (a : ℝ) : HasDerivAt normalCDF (normalPDF a) a := by
  have hc : Continuous normalPDF := contDiff_normalPDF.continuous
  have hi : Integrable normalPDF := integrable_gaussianPDFReal 0 1
  have he (y : ℝ) : normalCDF y = (∫ x in Iic (0 : ℝ), normalPDF x) +
      ∫ x in (0 : ℝ)..y, normalPDF x := by
    rw [normalCDF_eq_integral]
    have hh := intervalIntegral.integral_Iic_sub_Iic
      (a := 0) (b := y) hi.integrableOn hi.integrableOn
    linarith
  have h := (intervalIntegral.integral_hasDerivAt_right (a := 0) (b := a) hi.intervalIntegrable
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add
      (∫ x in Iic (0 : ℝ), normalPDF x)
  exact h.congr_of_eventuallyEq (Eventually.of_forall he)

/-- The density derivative is minus the coordinate times the density. -/
theorem hasDerivAt_normalPDF (a : ℝ) :
    HasDerivAt normalPDF (-a * normalPDF a) a := by
  have h := ((((hasDerivAt_id a).pow 2).neg.div_const (2 : ℝ)).exp).const_mul
    ((Real.sqrt (2 * Real.pi))⁻¹)
  convert! h using 1
  · funext y
    simp [normalPDF, gaussianPDFReal]
  · simp [normalPDF, gaussianPDFReal]
    ring

/-- Positivity makes the quotient defining the hazard well-defined. -/
theorem gaussianHazard_pos (a : ℝ) : 0 < gaussianHazard a :=
  div_pos (normalPDF_pos a) (normalCDF_pos (-a))

/-- The first identity in equation (2.3): `q' = q (q-a)`. -/
theorem hasDerivAt_gaussianHazard (a : ℝ) :
    HasDerivAt gaussianHazard (gaussianHazard a * (gaussianHazard a - a)) a := by
  have hc : HasDerivAt (fun x => normalCDF (-x)) (-normalPDF a) a := by
    convert! (hasDerivAt_normalCDF (-a)).comp a (hasDerivAt_id a).neg using 1
    simp [normalPDF_neg]
  have h := (hasDerivAt_normalPDF a).div hc (ne_of_gt (normalCDF_pos (-a)))
  convert! h using 1
  unfold gaussianHazard
  field_simp [ne_of_gt (normalCDF_pos (-a))]
  ring

/-- The scalar transport has derivative `q`. -/
theorem hasDerivAt_exponentialTransport (a : ℝ) :
    HasDerivAt exponentialTransport (gaussianHazard a) a := by
  have hc : HasDerivAt (fun x => normalCDF (-x)) (-normalPDF a) a := by
    convert! (hasDerivAt_normalCDF (-a)).comp a (hasDerivAt_id a).neg using 1
    simp [normalPDF_neg]
  convert! (hc.log (ne_of_gt (normalCDF_pos (-a)))).neg using 1
  simp [gaussianHazard, neg_div]

/-- Smoothness of the CDF follows from its smooth positive derivative. -/
theorem contDiff_normalCDF : ContDiff ℝ ∞ normalCDF := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun a => (hasDerivAt_normalCDF a).differentiableAt, ?_⟩
  have h : deriv normalCDF = normalPDF := funext fun a => (hasDerivAt_normalCDF a).deriv
  rw [h]
  exact contDiff_normalPDF

/-- Smoothness of the hazard on the whole real line. -/
theorem contDiff_gaussianHazard : ContDiff ℝ ∞ gaussianHazard := by
  exact contDiff_normalPDF.div (contDiff_normalCDF.comp contDiff_id.neg)
    (fun a => ne_of_gt (normalCDF_pos (-a)))

/-- Smoothness of the scalar transport on the whole real line. -/
theorem contDiff_exponentialTransport : ContDiff ℝ ∞ exponentialTransport := by
  exact ((contDiff_normalCDF.comp contDiff_id.neg).log
    (fun a => ne_of_gt (normalCDF_pos (-a)))).neg

/-- The paper's `d = q-a`. -/
noncomputable def gaussianGap (a : ℝ) : ℝ := gaussianHazard a - a

/-- The paper's `k = t/q`. -/
noncomputable def transportRatio (a : ℝ) : ℝ := exponentialTransport a / gaussianHazard a

/-- The expression for `b = k'`. -/
noncomputable def transportSlope (a : ℝ) : ℝ := 1 - transportRatio a * gaussianGap a

/-- The expression for `l = b'`. -/
noncomputable def transportCurvature (a : ℝ) : ℝ :=
  transportRatio a - gaussianHazard a + a * transportSlope a

/-- Derivative of the gap. -/
theorem hasDerivAt_gaussianGap (a : ℝ) :
    HasDerivAt gaussianGap (gaussianHazard a * gaussianGap a - 1) a := by
  exact (hasDerivAt_gaussianHazard a).sub (hasDerivAt_id a)

/-- The second identity in equation (2.3): `k' = 1-kd`. -/
theorem hasDerivAt_transportRatio (a : ℝ) :
    HasDerivAt transportRatio (transportSlope a) a := by
  have h := (hasDerivAt_exponentialTransport a).div (hasDerivAt_gaussianHazard a)
    (ne_of_gt (gaussianHazard_pos a))
  convert! h using 1
  unfold transportSlope transportRatio gaussianGap
  field_simp [ne_of_gt (gaussianHazard_pos a)]

/-- The third identity in equation (2.3): `b' = k-q+ab`. -/
theorem hasDerivAt_transportSlope (a : ℝ) :
    HasDerivAt transportSlope (transportCurvature a) a := by
  have h := ((hasDerivAt_transportRatio a).mul (hasDerivAt_gaussianGap a)).const_sub 1
  convert! h using 1
  unfold transportCurvature transportSlope gaussianGap
  ring

/-- The scalar relation used in the covariance completion. -/
theorem gaussianHazard_mul_transportRatio (a : ℝ) :
    gaussianHazard a * transportRatio a = exponentialTransport a := by
  unfold transportRatio
  exact mul_div_cancel₀ _ (ne_of_gt (gaussianHazard_pos a))

/-- Evenness of the normal density gives the CDF reflection identity. -/
theorem normalCDF_add_neg (a : ℝ) : normalCDF a + normalCDF (-a) = 1 := by
  have hi : Integrable normalPDF := integrable_gaussianPDFReal 0 1
  rw [normalCDF_eq_integral, normalCDF_eq_integral]
  have hneg : (∫ x in Iic (-a), normalPDF x) = ∫ x in Ioi a, normalPDF x := by
    simpa only [normalPDF_neg, neg_neg] using integral_comp_neg_Iic (-a) normalPDF
  rw [hneg, intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn]
  exact integral_gaussianPDFReal_eq_one 0 one_ne_zero

/-- The CDF stays strictly below one at every finite threshold. -/
theorem normalCDF_lt_one (a : ℝ) : normalCDF a < 1 := by
  linarith [normalCDF_pos (-a), normalCDF_add_neg a]

/-- The symmetry value of the standard normal CDF. -/
theorem normalCDF_zero : normalCDF 0 = 1 / 2 := by
  have h := normalCDF_add_neg 0
  simp only [neg_zero] at h
  linarith

end Submission.Obl.Entropy__lower_bound
