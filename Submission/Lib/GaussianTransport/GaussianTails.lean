/-
Adapted from: here:o001

Original Section 2.1 scalar proofs by session x0004.
-/

import Submission.Lib.GaussianTransport.GaussianModel

/-! Tail-integral identities for the Mills-ratio argument in Lemma 2.1. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff

namespace Submission.Lib.GaussianTransport

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

/-- Strict monotonicity of the Gaussian hazard. -/
theorem strictMono_gaussianHazard : StrictMono gaussianHazard :=
  strictMono_of_deriv_pos deriv_gaussianHazard_pos

/-- The standard normal density also tends to zero at negative infinity. -/
theorem tendsto_normalPDF_atBot : Tendsto normalPDF atBot (𝓝 0) := by
  simpa only [Function.comp_def, normalPDF_neg] using
    tendsto_normalPDF_atTop.comp tendsto_neg_atBot_atTop

/-- The lower endpoint of the range of the Gaussian hazard. -/
theorem tendsto_gaussianHazard_atBot : Tendsto gaussianHazard atBot (𝓝 0) := by
  have hcdf : Tendsto (fun a => normalCDF (-a)) atBot (𝓝 1) :=
    (tendsto_cdf_atTop (gaussianReal 0 1)).comp tendsto_neg_atBot_atTop
  convert! tendsto_normalPDF_atBot.div hcdf one_ne_zero using 1
  simp

/-- The hazard tends to infinity because it is strictly above the coordinate. -/
theorem tendsto_gaussianHazard_atTop : Tendsto gaussianHazard atTop atTop :=
  tendsto_atTop_mono (fun a => (sub_pos.mp (gaussianGap_pos a)).le) tendsto_id

/-- The Gaussian hazard is onto the positive real numbers. -/
theorem range_gaussianHazard : Set.range gaussianHazard = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact gaussianHazard_pos a
  · intro hy
    obtain ⟨a, ha⟩ := (tendsto_gaussianHazard_atBot.eventually_lt_const hy).exists
    exact intermediate_value_univ a y contDiff_gaussianHazard.continuous
      ⟨ha.le, (sub_pos.mp (gaussianGap_pos y)).le⟩

/-- Gaussian integration by parts for the second unnormalized tail moment. -/
theorem integral_sq_mul_normalPDF_tail (a : ℝ) :
    (∫ x in Ioi a, x ^ 2 * normalPDF x) = a * normalPDF a + normalCDF (-a) := by
  have hp : Integrable normalPDF := integrable_gaussianPDFReal 0 1
  have hi : Integrable (fun x => x * normalPDF x) := by
    simpa only [pow_one] using integrable_pow_mul_normalPDF 1
  have hi2 := integrable_pow_mul_normalPDF 2
  have hd (x : ℝ) : HasDerivAt (fun x => x * normalPDF x)
      (normalPDF x - x ^ 2 * normalPDF x) x := by
    convert! (hasDerivAt_id x).mul (hasDerivAt_normalPDF x) using 1
    simp only [id_eq, one_mul]
    ring
  have ht : Tendsto (fun x => x * normalPDF x) atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0) (fun x _ => hd x)
      (hp.sub hi2).integrableOn hi.integrableOn
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x)
    (hp.sub hi2).integrableOn ht (a := a)
  rw [integral_sub hp.integrableOn hi2.integrableOn, ← normalCDF_neg_eq_tail] at h
  linarith

private theorem integrable_centered_sq_normalPDF (c : ℝ) :
    Integrable (fun x => (x - c) ^ 2 * normalPDF x) := by
  have hp : Integrable normalPDF := integrable_gaussianPDFReal 0 1
  have hi : Integrable (fun x => x * normalPDF x) := by
    simpa only [pow_one] using integrable_pow_mul_normalPDF 1
  have h := ((integrable_pow_mul_normalPDF 2).sub (hi.const_mul (2 * c))).add
    (hp.const_mul (c ^ 2))
  convert! h using 1
  funext x
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- A Gaussian tail has strictly positive variance about any proposed center. -/
theorem integral_centered_sq_normalPDF_tail_pos (a c : ℝ) :
    0 < ∫ x in Ioi a, (x - c) ^ 2 * normalPDF x := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (fun x => mul_nonneg (sq_nonneg _) (normalPDF_pos x).le))
    (integrable_centered_sq_normalPDF c).integrableOn).2
  have hs : Ioi (max a c) ⊆
      Function.support (fun x => (x - c) ^ 2 * normalPDF x) ∩ Ioi a := by
    intro x hx
    have ha : a < x := (le_max_left a c).trans_lt hx
    have hc : c < x := (le_max_right a c).trans_lt hx
    refine ⟨?_, ha⟩
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (ne_of_gt hc)))
      (ne_of_gt (normalPDF_pos x))
  have hmeasure := measure_mono (μ := volume) hs
  rw [Real.volume_Ioi] at hmeasure
  exact ENNReal.zero_lt_top.trans_le hmeasure

/-- Exact raw-moment expansion of the centered tail second moment. -/
theorem integral_centered_sq_normalPDF_tail (a c : ℝ) :
    (∫ x in Ioi a, (x - c) ^ 2 * normalPDF x) =
      a * normalPDF a + normalCDF (-a) - 2 * c * normalPDF a + c ^ 2 * normalCDF (-a) := by
  have hp : Integrable normalPDF := integrable_gaussianPDFReal 0 1
  have hi : Integrable (fun x => x * normalPDF x) := by
    simpa only [pow_one] using integrable_pow_mul_normalPDF 1
  have hi2 := integrable_pow_mul_normalPDF 2
  calc
    _ = ∫ x in Ioi a, (x ^ 2 * normalPDF x - (2 * c) * (x * normalPDF x)) +
        c ^ 2 * normalPDF x := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = _ := by
      have hs := integral_sub (μ := volume.restrict (Ioi a)) hi2.integrableOn (hi.const_mul (2 * c)).integrableOn
      have ha := integral_add (μ := volume.restrict (Ioi a)) (hi2.sub (hi.const_mul (2 * c))).integrableOn
        (hp.const_mul (c ^ 2)).integrableOn
      simp only [Pi.sub_apply] at ha
      rw [ha, hs, integral_const_mul, integral_const_mul,
        integral_sq_mul_normalPDF_tail, integral_mul_normalPDF_tail, ← normalCDF_neg_eq_tail]

/-- The positive conditional variance in the proof of Lemma 2.1. -/
theorem one_sub_hazard_mul_gap_pos (a : ℝ) :
    0 < 1 - gaussianHazard a * gaussianGap a := by
  have h := integral_centered_sq_normalPDF_tail_pos a (gaussianHazard a)
  rw [integral_centered_sq_normalPDF_tail] at h
  have hp : normalPDF a = gaussianHazard a * normalCDF (-a) := by
    unfold gaussianHazard
    rw [div_mul_cancel₀ _ (ne_of_gt (normalCDF_pos (-a)))]
  rw [hp] at h
  have hfactor :
      a * (gaussianHazard a * normalCDF (-a)) + normalCDF (-a) -
        2 * gaussianHazard a * (gaussianHazard a * normalCDF (-a)) +
          gaussianHazard a ^ 2 * normalCDF (-a) =
      normalCDF (-a) * (1 - gaussianHazard a * gaussianGap a) := by
    unfold gaussianGap
    ring
  rw [hfactor] at h
  exact (mul_pos_iff_of_pos_left (normalCDF_pos (-a))).mp h

/-- The upper derivative bound in Lemma 2.1. -/
theorem deriv_gaussianHazard_lt_one (a : ℝ) : deriv gaussianHazard a < 1 := by
  rw [(hasDerivAt_gaussianHazard a).deriv]
  have h := one_sub_hazard_mul_gap_pos a
  unfold gaussianGap at h
  linarith

/-- The scalar spectral parameter is globally 1-Lipschitz. -/
theorem lipschitzWith_gaussianHazard : LipschitzWith 1 gaussianHazard := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun a => (hasDerivAt_gaussianHazard a).differentiableAt)
  intro a
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, Real.norm_eq_abs,
    abs_of_pos (deriv_gaussianHazard_pos a)]
  exact (deriv_gaussianHazard_lt_one a).le

/-- Monotonicity of the hazard gives the survival comparison used in Lemma 2.1. -/
theorem gaussian_survival_submultiplicative (a u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    normalCDF (-(a + (u + v))) / normalCDF (-a) ≤
      (normalCDF (-(a + u)) / normalCDF (-a)) *
        (normalCDF (-(a + v)) / normalCDF (-a)) := by
  have hd (x : ℝ) :
      HasDerivAt (fun x => exponentialTransport (x + v) - exponentialTransport x)
        (gaussianHazard (x + v) - gaussianHazard x) x := by
    convert! ((hasDerivAt_exponentialTransport (x + v)).comp x
      ((hasDerivAt_id x).add_const v)).sub (hasDerivAt_exponentialTransport x) using 1
    simp
  have hm : Monotone (fun x => exponentialTransport (x + v) - exponentialTransport x) :=
    monotone_of_hasDerivAt_nonneg hd (fun x => sub_nonneg.mpr
      (strictMono_gaussianHazard.monotone (le_add_of_nonneg_right hv)))
  have hdiff := hm (a := a) (b := a + u) (le_add_of_nonneg_right hu)
  have hcdf (x : ℝ) : normalCDF (-x) = Real.exp (-exponentialTransport x) := by
    unfold exponentialTransport
    rw [neg_neg, Real.exp_log (normalCDF_pos (-x))]
  rw [hcdf, hcdf, hcdf, hcdf, ← Real.exp_sub, ← Real.exp_sub, ← Real.exp_sub,
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [add_assoc] at hdiff
  linarith

end Submission.Lib.GaussianTransport
