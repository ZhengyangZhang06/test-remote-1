import Submission.Obl.Entropy__lower_bound.GaussianModel

/-! Tail-integral identities for the Mills-ratio argument in Lemma 2.1. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff

namespace Submission.Obl.Entropy__lower_bound

/-- Every polynomial moment of the standard Gaussian density is integrable. -/
theorem integrable_pow_mul_normalPDF (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n * normalPDF x) := by
  have h := (integrable_rpow_mul_exp_neg_mul_sq
    (by norm_num : (0 : ℝ) < 1 / 2) (s := (n : ℝ)) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)).const_mul
      ((Real.sqrt (2 * Real.pi))⁻¹)
  convert! h using 1
  funext x
  simp only [normalPDF, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one, Real.rpow_natCast]
  ring_nf

/-- The standard Gaussian density tends to zero at positive infinity. -/
theorem tendsto_normalPDF_atTop : Tendsto normalPDF atTop (𝓝 0) := by
  have h := Real.tendsto_exp_atBot.comp
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop_of_neg
      (by norm_num : -(1 / 2 : ℝ) < 0))
  have h' := h.const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
  convert! h' using 1
  · funext x
    simp only [normalPDF, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one,
      Function.comp_apply]
    congr 1
    congr 1
    ring
  · simp

/-- The survival probability is the reflected CDF. -/
theorem normalCDF_neg_eq_tail (a : ℝ) :
    normalCDF (-a) = ∫ x in Ioi a, normalPDF x := by
  rw [normalCDF_eq_integral]
  simpa only [normalPDF_neg, neg_neg] using integral_comp_neg_Iic (-a) normalPDF

/-- Gaussian integration by parts for the first unnormalized tail moment. -/
theorem integral_mul_normalPDF_tail (a : ℝ) :
    (∫ x in Ioi a, x * normalPDF x) = normalPDF a := by
  have hd (x : ℝ) : HasDerivAt (fun x => -normalPDF x) (x * normalPDF x) x := by
    convert! (hasDerivAt_normalPDF x).neg using 1
    simp only [neg_mul, neg_neg]
  have hi : Integrable (fun x => x * normalPDF x) := by
    simpa only [pow_one] using integrable_pow_mul_normalPDF 1
  have ht : Tendsto (fun x => -normalPDF x) atTop (𝓝 0) := by
    simpa using tendsto_normalPDF_atTop.neg
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x) hi.integrableOn ht

/-- A Gaussian tail has mean strictly above its truncation point. -/
theorem normalPDF_sub_mul_normalCDF_pos (a : ℝ) :
    0 < normalPDF a - a * normalCDF (-a) := by
  have hi : Integrable (fun x => x * normalPDF x) := by
    simpa only [pow_one] using integrable_pow_mul_normalPDF 1
  have hp : Integrable normalPDF := integrable_gaussianPDFReal 0 1
  have hg : Integrable (fun x => x * normalPDF x - a * normalPDF x) :=
    hi.sub (hp.const_mul a)
  have hpos (x : ℝ) (hx : x ∈ Ioi a) :
      0 < x * normalPDF x - a * normalPDF x := by
    exact sub_pos.mpr (mul_lt_mul_of_pos_right hx (normalPDF_pos x))
  have hn : ∀ᵐ x ∂volume.restrict (Ioi a),
      0 ≤ x * normalPDF x - a * normalPDF x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (hpos x hx).le
  have hs : Function.support (fun x => x * normalPDF x - a * normalPDF x) ∩ Ioi a =
      Ioi a := by
    ext x
    simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
    exact ⟨fun hx => hx.2, fun hx => ⟨ne_of_gt (hpos x hx), hx⟩⟩
  have hgt : 0 < ∫ x in Ioi a, x * normalPDF x - a * normalPDF x := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae hn hg.integrableOn).2
    rw [hs, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  rw [integral_sub hi.integrableOn (hp.const_mul a).integrableOn,
    integral_const_mul, integral_mul_normalPDF_tail, ← normalCDF_neg_eq_tail] at hgt
  exact hgt

/-- The positive gap in Lemma 2.1. -/
theorem gaussianGap_pos (a : ℝ) : 0 < gaussianGap a := by
  unfold gaussianGap gaussianHazard
  rw [sub_pos, lt_div_iff₀ (normalCDF_pos (-a))]
  exact sub_pos.mp (normalPDF_sub_mul_normalCDF_pos a)

/-- Strict positivity of the hazard derivative. -/
theorem deriv_gaussianHazard_pos (a : ℝ) : 0 < deriv gaussianHazard a := by
  rw [(hasDerivAt_gaussianHazard a).deriv]
  exact mul_pos (gaussianHazard_pos a) (gaussianGap_pos a)

end Submission.Obl.Entropy__lower_bound
