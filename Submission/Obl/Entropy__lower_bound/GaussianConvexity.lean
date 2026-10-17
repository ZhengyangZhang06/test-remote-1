import Submission.Obl.Entropy__lower_bound.GaussianTails

/-!
The integrated tail comparison in Lemma 2.1 of the supplied paper.
We integrate the decreasing conditional excess mean, which is the once-integrated
survival comparison. Explicit antiderivatives avoid a separate product integral.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff

namespace Submission.Obl.Entropy__lower_bound

/-- The positive conditional variance makes the Gaussian excess mean decrease strictly. -/
theorem strictAnti_gaussianGap : StrictAnti gaussianGap := by
  apply strictAnti_of_deriv_neg
  intro a
  rw [(hasDerivAt_gaussianGap a).deriv]
  have h := one_sub_hazard_mul_gap_pos a
  linarith

theorem antitone_gaussianGap : Antitone gaussianGap := strictAnti_gaussianGap.antitone

private theorem hasDerivAt_survival (a : ℝ) :
    HasDerivAt (fun x => normalCDF (-x)) (-normalPDF a) a := by
  convert! (hasDerivAt_normalCDF (-a)).comp a (hasDerivAt_id a).neg using 1
  simp [normalPDF_neg]

private theorem tendsto_mul_normalPDF :
    Tendsto (fun x => x * normalPDF x) atTop (𝓝 0) := by
  have hd (x : ℝ) : HasDerivAt (fun x => x * normalPDF x)
      (normalPDF x - x ^ 2 * normalPDF x) x := by
    convert! (hasDerivAt_id x).mul (hasDerivAt_normalPDF x) using 1
    simp only [id_eq, one_mul]
    ring
  have hp : Integrable normalPDF := integrable_gaussianPDFReal 0 1
  have hi : Integrable (fun x => x * normalPDF x) := by
    simpa only [pow_one] using integrable_pow_mul_normalPDF 1
  exact tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
    (fun x _ => hd x) (hp.sub (integrable_pow_mul_normalPDF 2)).integrableOn
      hi.integrableOn

private theorem tendsto_mul_survival :
    Tendsto (fun x => x * normalCDF (-x)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ tendsto_normalPDF_atTop
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact mul_nonneg hx (normalCDF_pos (-x)).le
  · exact Eventually.of_forall fun x => (sub_pos.mp
      (normalPDF_sub_mul_normalCDF_pos x)).le

private theorem tendsto_sq_mul_survival :
    Tendsto (fun x => x ^ 2 * normalCDF (-x)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ tendsto_mul_normalPDF
  · exact Eventually.of_forall fun x =>
      mul_nonneg (sq_nonneg x) (normalCDF_pos (-x)).le
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have h := mul_le_mul_of_nonneg_left
      (sub_pos.mp (normalPDF_sub_mul_normalCDF_pos x)).le hx
    nlinarith

private theorem hasDerivAt_excess_antiderivative (a : ℝ) :
    HasDerivAt (fun x => x * normalCDF (-x) - normalPDF x) (normalCDF (-a)) a := by
  convert! ((hasDerivAt_id a).mul (hasDerivAt_survival a)).sub
    (hasDerivAt_normalPDF a) using 1
  simp only [id_eq, one_mul]
  ring

private theorem tendsto_excess_antiderivative :
    Tendsto (fun x => x * normalCDF (-x) - normalPDF x) atTop (𝓝 0) := by
  simpa using tendsto_mul_survival.sub tendsto_normalPDF_atTop

/-- Integrability of the Gaussian survival function on every right half-line. -/
theorem integrableOn_normalCDF_neg (a : ℝ) :
    IntegrableOn (fun x => normalCDF (-x)) (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun x _ => hasDerivAt_excess_antiderivative x)
    (fun x _ => (normalCDF_pos (-x)).le) tendsto_excess_antiderivative

/-- The unnormalized conditional excess mean, expressed as a survival integral. -/
theorem integral_normalCDF_neg_tail (a : ℝ) :
    (∫ x in Ioi a, normalCDF (-x)) = normalPDF a - a * normalCDF (-a) := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ => hasDerivAt_excess_antiderivative x)
    (integrableOn_normalCDF_neg a) tendsto_excess_antiderivative
  simpa only [zero_sub, neg_sub] using h

private theorem hasDerivAt_second_excess_antiderivative (a : ℝ) :
    HasDerivAt (fun x => (x * normalPDF x - (x ^ 2 + 1) * normalCDF (-x)) / 2)
      (normalPDF a - a * normalCDF (-a)) a := by
  convert! (((hasDerivAt_id a).mul (hasDerivAt_normalPDF a)).sub
    ((((hasDerivAt_id a).pow 2).add_const 1).mul (hasDerivAt_survival a))).div_const 2
      using 1
  simp only [Pi.pow_apply, id_eq, one_mul]
  ring

private theorem tendsto_second_excess_antiderivative :
    Tendsto (fun x => (x * normalPDF x - (x ^ 2 + 1) * normalCDF (-x)) / 2)
      atTop (𝓝 0) := by
  have hsurv : Tendsto (fun x => normalCDF (-x)) atTop (𝓝 0) :=
    (tendsto_cdf_atBot (gaussianReal 0 1)).comp tendsto_neg_atTop_atBot
  have h := (tendsto_mul_normalPDF.sub (tendsto_sq_mul_survival.add hsurv)).div_const 2
  convert! h using 1
  · funext x
    ring
  · norm_num

/-- Integrability of the once-integrated Gaussian survival function. -/
theorem integrableOn_normalPDF_sub_mul_normalCDF (a : ℝ) :
    IntegrableOn (fun x => normalPDF x - x * normalCDF (-x)) (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun x _ => hasDerivAt_second_excess_antiderivative x)
    (fun x _ => (normalPDF_sub_mul_normalCDF_pos x).le)
    tendsto_second_excess_antiderivative

/-- The twice-integrated tail has an explicit second-moment expression. -/
theorem integral_normalPDF_sub_mul_normalCDF_tail (a : ℝ) :
    (∫ x in Ioi a, normalPDF x - x * normalCDF (-x)) =
      ((a ^ 2 + 1) * normalCDF (-a) - a * normalPDF a) / 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ => hasDerivAt_second_excess_antiderivative x)
    (integrableOn_normalPDF_sub_mul_normalCDF a) tendsto_second_excess_antiderivative
  convert! h using 1
  ring

/-- The variance of a Gaussian excess is strictly below its squared mean (Lemma 2.1). -/
theorem one_sub_hazard_mul_gap_lt_gap_sq (a : ℝ) :
    1 - gaussianHazard a * gaussianGap a < gaussianGap a ^ 2 := by
  have hfactor (x : ℝ) : normalPDF x - x * normalCDF (-x) =
      gaussianGap x * normalCDF (-x) := by
    unfold gaussianGap gaussianHazard
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt (normalCDF_pos (-x)))]
  let F : ℝ → ℝ := fun x => gaussianGap a * normalCDF (-x) -
    (normalPDF x - x * normalCDF (-x))
  have hF (x : ℝ) (hx : x ∈ Ioi a) : 0 < F x := by
    dsimp only [F]
    rw [hfactor]
    exact sub_pos.mpr (mul_lt_mul_of_pos_right (strictAnti_gaussianGap hx)
      (normalCDF_pos (-x)))
  have hint : IntegrableOn F (Ioi a) :=
    ((integrableOn_normalCDF_neg a).const_mul (gaussianGap a)).sub
      (integrableOn_normalPDF_sub_mul_normalCDF a)
  have hpos : 0 < ∫ x in Ioi a, F x := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact (hF x hx).le) hint).2
    have hs : Function.support F ∩ Ioi a = Ioi a := by
      ext x
      exact ⟨fun hx => hx.2, fun hx => ⟨ne_of_gt (hF x hx), hx⟩⟩
    rw [hs, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  have hi : (∫ x in Ioi a, normalPDF x - x * normalCDF (-x)) <
      ∫ x in Ioi a, gaussianGap a * normalCDF (-x) := by
    dsimp only [F] at hpos
    rw [integral_sub ((integrableOn_normalCDF_neg a).const_mul (gaussianGap a))
      (integrableOn_normalPDF_sub_mul_normalCDF a)] at hpos
    exact sub_pos.mp hpos
  rw [integral_normalPDF_sub_mul_normalCDF_tail, integral_const_mul,
    integral_normalCDF_neg_tail, hfactor] at hi
  have hpdf : normalPDF a = gaussianHazard a * normalCDF (-a) := by
    unfold gaussianHazard
    rw [div_mul_cancel₀ _ (ne_of_gt (normalCDF_pos (-a)))]
  rw [hpdf] at hi
  have hbound : (a ^ 2 + 1 - a * gaussianHazard a) / 2 < gaussianGap a ^ 2 := by
    apply (mul_lt_mul_iff_of_pos_right (normalCDF_pos (-a))).mp
    nlinarith [hi]
  unfold gaussianGap at *
  nlinarith

/-- The weak variance bound used in Lemma 2.1. -/
theorem one_sub_hazard_mul_gap_le_gap_sq (a : ℝ) :
    1 - gaussianHazard a * gaussianGap a ≤ gaussianGap a ^ 2 :=
  (one_sub_hazard_mul_gap_lt_gap_sq a).le

/-- Differentiating `q' = q d` gives the second derivative in Lemma 2.1. -/
theorem hasDerivAt_deriv_gaussianHazard (a : ℝ) :
    HasDerivAt (deriv gaussianHazard)
      (gaussianHazard a * (gaussianGap a ^ 2 + gaussianHazard a * gaussianGap a - 1)) a := by
  have hq : deriv gaussianHazard = fun x => gaussianHazard x * gaussianGap x :=
    funext fun x => (hasDerivAt_gaussianHazard x).deriv
  rw [hq]
  convert! (hasDerivAt_gaussianHazard a).mul (hasDerivAt_gaussianGap a) using 1
  unfold gaussianGap
  ring

theorem deriv2_gaussianHazard_nonneg (a : ℝ) : 0 ≤ deriv (deriv gaussianHazard) a := by
  rw [(hasDerivAt_deriv_gaussianHazard a).deriv]
  apply mul_nonneg (gaussianHazard_pos a).le
  have h := one_sub_hazard_mul_gap_le_gap_sq a
  linarith

theorem convexOn_gaussianHazard : ConvexOn ℝ univ gaussianHazard := by
  apply convexOn_of_deriv2_nonneg convex_univ contDiff_gaussianHazard.continuous.continuousOn
  · exact fun x _ => (hasDerivAt_gaussianHazard x).differentiableAt.differentiableWithinAt
  · exact fun x _ => (hasDerivAt_deriv_gaussianHazard x).differentiableAt.differentiableWithinAt
  · exact fun x _ => deriv2_gaussianHazard_nonneg x

end Submission.Obl.Entropy__lower_bound
