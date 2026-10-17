import Submission.Lib.ScalarLog.Cutoff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set
open Submission.Lib.EntropyTools

namespace Submission.Obl.Root.ScalarMinorant

noncomputable def minorantSlope (u : ℝ) : ℝ := u * Real.sqrt u / 2
noncomputable def minorantCurvature (u : ℝ) : ℝ := u ^ 3 / (16 * (23 / 50 - u))

lemma curvature_pos {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 13 / 100) :
    0 < minorantCurvature u := by
  have hd : 0 < 23 / 50 - u := by linarith
  unfold minorantCurvature
  positivity

/-- The negative half-line part of the quadratic minorant, before subtracting its quadratic term. -/
lemma reciprocal_minorant_negative {u a : ℝ} (hu0 : 0 < u) (hu : u ≤ 13 / 100) (ha : a ≤ 0) :
    u + minorantSlope u * a ≤ 1 / (7 + a ^ 2) := by
  let x := -Real.sqrt u * a
  have hx : 0 ≤ x := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (Real.sqrt_nonneg u)) ha
  have hx2 : x ^ 2 = u * a ^ 2 := by
    dsimp [x]
    rw [mul_pow, neg_sq, Real.sq_sqrt hu0.le]
  have hb : u + minorantSlope u * a = u * (1 - x / 2) := by
    dsimp [minorantSlope, x]
    ring
  by_cases hsmall : x ≤ 2
  · have he : 1 - (1 - x / 2) * (x ^ 2 + 7 * u) =
        x * (x - 1) ^ 2 / 2 + (9 / 200) * (2 - x) +
          7 * (13 / 100 - u) * (1 - x / 2) := by ring
    have hnonneg : 0 ≤ 1 - (1 - x / 2) * (x ^ 2 + 7 * u) := by
      rw [he]
      have h1 : 0 ≤ 2 - x := by linarith
      have h2 : 0 ≤ 13 / 100 - u := by linarith
      have h3 : 0 ≤ 1 - x / 2 := by linarith
      positivity
    apply (le_div_iff₀ (by positivity : 0 < 7 + a ^ 2)).mpr
    calc
      (u + minorantSlope u * a) * (7 + a ^ 2) =
          (1 - x / 2) * (u * a ^ 2 + 7 * u) := by rw [hb]; ring
      _ = (1 - x / 2) * (x ^ 2 + 7 * u) := by rw [hx2]
      _ ≤ 1 := by linarith
  · have hbase : u + minorantSlope u * a ≤ 0 := by
      rw [hb]
      exact mul_nonpos_of_nonneg_of_nonpos hu0.le (by linarith)
    exact hbase.trans (by positivity)

lemma slope_square {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 13 / 100) :
    minorantSlope u ^ 2 = 4 * minorantCurvature u * (23 / 50 - u) := by
  have hd : 23 / 50 - u ≠ 0 := by linarith
  have hd' : (23 : ℝ) - u * 50 ≠ 0 := by linarith
  unfold minorantSlope minorantCurvature
  rw [div_pow, mul_pow, Real.sq_sqrt hu0.le]
  field_simp [hd']
  ring

lemma quadratic_le_tail {u a : ℝ} (hu0 : 0 < u) (hu : u ≤ 13 / 100) :
    u + minorantSlope u * a - minorantCurvature u * a ^ 2 ≤ 23 / 50 := by
  have hd := curvature_pos hu0 hu
  have hs := slope_square hu0 hu
  have hn := sq_nonneg (2 * minorantCurvature u * a - minorantSlope u)
  have hprod : 0 ≤ (23 / 50 - (u + minorantSlope u * a - minorantCurvature u * a ^ 2)) *
      (4 * minorantCurvature u) := by nlinarith only [hn, hs]
  have h := nonneg_of_mul_nonneg_left hprod (by positivity : 0 < 4 * minorantCurvature u)
  linarith

/-- Equation (4.4), using precisely the three pointwise lower bounds for `p`. -/
theorem quadratic_minorant (p : ℝ → ℝ)
    (hneg : ∀ a ≤ 0, 1 / (7 + a ^ 2) ≤ p a)
    (hpos : ∀ a, 0 ≤ a → 1 / 4 ≤ p a)
    (htail : ∀ a, 4 ≤ a → 23 / 50 ≤ p a)
    {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 13 / 100) (a : ℝ) :
    u + minorantSlope u * a - minorantCurvature u * a ^ 2 ≤ p a := by
  have hd := curvature_pos hu0 hu
  have hquad : 0 ≤ minorantCurvature u * a ^ 2 := mul_nonneg hd.le (sq_nonneg a)
  by_cases ha : a ≤ 0
  · exact (sub_le_self _ hquad).trans ((reciprocal_minorant_negative hu0 hu ha).trans (hneg a ha))
  by_cases hlarge : 4 ≤ a
  · exact (quadratic_le_tail hu0 hu).trans (htail a hlarge)
  have hasmall : a ≤ 4 := (not_le.mp hlarge).le
  have hsqrt : Real.sqrt u ≤ 37 / 100 := by
    nlinarith [Real.sq_sqrt hu0.le, Real.sqrt_nonneg u]
  have hmul : u * Real.sqrt u ≤ (13 / 100 : ℝ) * (37 / 100) :=
    mul_le_mul hu hsqrt (Real.sqrt_nonneg u) (by norm_num)
  have hslope : minorantSlope u ≤ 481 / 20000 := by unfold minorantSlope; linarith
  have hslope0 : 0 ≤ minorantSlope u := by unfold minorantSlope; positivity
  have hlin := mul_le_mul_of_nonneg_left hasmall hslope0
  have hp := hpos a (not_le.mp ha).le
  nlinarith

lemma cutoff_le {lam : ℝ} : rigidityCutoff lam ≤ 13 / 100 := by
  unfold rigidityCutoff
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

lemma cutoff_square_mul_le {lam : ℝ} (hlam : 0 ≤ lam) :
    lam * rigidityCutoff lam ^ 2 ≤ (32 / 25 : ℝ) ^ 2 := by
  by_cases hz : lam = 0
  · subst lam; norm_num
  have hsqrt : 0 < Real.sqrt lam := Real.sqrt_pos.mpr (lt_of_le_of_ne hlam (Ne.symm hz))
  have hu : rigidityCutoff lam ≤ 32 / (25 * Real.sqrt lam) := by
    rw [rigidityCutoff, if_neg hz]
    exact min_le_right _ _
  have hh : rigidityCutoff lam * Real.sqrt lam ≤ 32 / 25 := by
    apply (le_div_iff₀ hsqrt).mp
    simpa only [div_div] using hu
  have hsq := pow_le_pow_left₀ (mul_nonneg (rigidityCutoff_pos hlam).le hsqrt.le) hh 2
  rw [mul_pow, Real.sq_sqrt hlam] at hsq
  nlinarith

/-- Loss in the first- and second-moment minorant: `d_u * lambda <= .311*u`. -/
lemma curvature_mul_le {u lam : ℝ} (hu0 : 0 < u) (hu : u ≤ 13 / 100)
    (hlim : lam * u ^ 2 ≤ (32 / 25 : ℝ) ^ 2) :
    minorantCurvature u * lam ≤ (311 / 1000) * u := by
  have hd : 0 < 16 * (23 / 50 - u) := by linarith
  unfold minorantCurvature
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).mpr
  have hmult := mul_le_mul_of_nonneg_right hlim hu0.le
  have hrest := mul_nonneg hu0.le (sub_nonneg.mpr hu)
  nlinarith

/-- Integrating the quadratic minorant against a probability law. -/
theorem integral_lower_bound (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ → ℝ)
    (hneg : ∀ a ≤ 0, 1 / (7 + a ^ 2) ≤ p a)
    (hpos : ∀ a, 0 ≤ a → 1 / 4 ≤ p a)
    (htail : ∀ a, 4 ≤ a → 23 / 50 ≤ p a)
    (hp : Integrable p μ) (hfirst : Integrable (fun a : ℝ => a) μ)
    (hsecond : Integrable (fun a : ℝ => a ^ 2) μ)
    (hmean : ∫ a, a ∂μ = 0) {u lam r : ℝ}
    (hmoment : ∫ a, a ^ 2 ∂μ = lam + r) (hu0 : 0 < u) (hu : u ≤ 13 / 100) :
    u - minorantCurvature u * (lam + r) ≤ ∫ a, p a ∂μ := by
  have hsum : Integrable (fun a : ℝ => u + minorantSlope u * a) μ :=
    (integrable_const u).add (hfirst.const_mul (minorantSlope u))
  have hquad := hsecond.const_mul (minorantCurvature u)
  have hb := integral_mono_ae (hsum.sub hquad) hp
    (Filter.Eventually.of_forall (quadratic_minorant p hneg hpos htail hu0 hu))
  change (∫ a, (u + minorantSlope u * a) - minorantCurvature u * a ^ 2 ∂μ) ≤ ∫ a, p a ∂μ at hb
  rw [integral_sub hsum hquad, integral_add (integrable_const u)
    (hfirst.const_mul (minorantSlope u))] at hb
  have hlinear : (∫ a, minorantSlope u * a ∂μ) = 0 := by
    have hh := integral_const_mul (μ := μ) (minorantSlope u) (fun a : ℝ => a)
    rw [hmean, mul_zero] at hh
    exact hh
  simpa only [integral_const, integral_const_mul, hlinear, hmean, hmoment, mul_zero, add_zero,
    probReal_univ, one_smul] using hb

/-- Equation (4.5) of the paper, retaining the higher-chaos second moment. -/
theorem integral_lower_bound_cutoff (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ → ℝ)
    (hneg : ∀ a ≤ 0, 1 / (7 + a ^ 2) ≤ p a)
    (hpos : ∀ a, 0 ≤ a → 1 / 4 ≤ p a)
    (htail : ∀ a, 4 ≤ a → 23 / 50 ≤ p a)
    (hp : Integrable p μ) (hfirst : Integrable (fun a : ℝ => a) μ)
    (hsecond : Integrable (fun a : ℝ => a ^ 2) μ)
    (hmean : ∫ a, a ∂μ = 0) {lam r : ℝ} (hlam : 0 ≤ lam)
    (hmoment : ∫ a, a ^ 2 ∂μ = lam + r) :
    (689 / 1000) * rigidityCutoff lam - minorantCurvature (rigidityCutoff lam) * r ≤
      ∫ a, p a ∂μ := by
  have hb := integral_lower_bound μ p hneg hpos htail hp hfirst hsecond hmean hmoment
    (rigidityCutoff_pos hlam) cutoff_le
  have hloss := curvature_mul_le (rigidityCutoff_pos hlam) cutoff_le (cutoff_square_mul_le hlam)
  nlinarith

lemma curvature_le {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 13 / 100) :
    minorantCurvature u ≤ 1 / 1000 := by
  have hd : 0 < 16 * (23 / 50 - u) := by linarith
  have hpow := pow_le_pow_left₀ hu0.le hu 3
  unfold minorantCurvature
  apply (div_le_iff₀ hd).mpr
  nlinarith

/-- The scalar product `H*rho` in the first-chaos absorption argument. -/
noncomputable def absorptionFactor (lam : ℝ) : ℝ :=
  (3 * (lam - 1) ^ 2 / (37 + 3 * lam)) * (3 / 20 + 49 / 100 * (37 / (37 + 3 * lam)))

lemma absorptionFactor_nonneg {lam : ℝ} (hlam : 0 ≤ lam) : 0 ≤ absorptionFactor lam := by
  dsimp [absorptionFactor]
  positivity

lemma absorptionFactor_le {lam : ℝ} (hlam : 0 ≤ lam) :
    absorptionFactor lam ≤ (16 / 25) * max 1 lam := by
  have hd : 0 < 37 + 3 * lam := by positivity
  have hratio : 37 / (37 + 3 * lam) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ hd).mpr
    linarith
  have hrho : (3 / 20 : ℝ) + 49 / 100 * (37 / (37 + 3 * lam)) ≤ 16 / 25 := by linarith
  have hH : 3 * (lam - 1) ^ 2 / (37 + 3 * lam) ≤ max 1 lam := by
    apply (div_le_iff₀ hd).mpr
    by_cases hl : lam ≤ 1
    · rw [max_eq_left hl]
      nlinarith [mul_nonneg hlam (sub_nonneg.mpr hl)]
    · rw [max_eq_right (not_le.mp hl).le]
      nlinarith
  have hm : 0 ≤ max (1 : ℝ) lam := le_trans (by norm_num) (le_max_left _ _)
  exact (mul_le_mul hH hrho (by positivity) hm).trans_eq (mul_comm _ _)

/-- Equation (4.6): the cost of the residual second moment is at most `.027`. -/
lemma factor_curvature_le {lam : ℝ} (hlam : 0 ≤ lam) :
    absorptionFactor lam * minorantCurvature (rigidityCutoff lam) ≤ 27 / 1000 := by
  have hu0 := rigidityCutoff_pos hlam
  have hdu := curvature_pos hu0 cutoff_le
  have hfactor := absorptionFactor_le hlam
  have hmul := mul_le_mul_of_nonneg_right hfactor hdu.le
  by_cases hl : lam ≤ 1
  · rw [max_eq_left hl] at hmul
    have hc := curvature_le hu0 cutoff_le
    nlinarith
  · rw [max_eq_right (not_le.mp hl).le] at hmul
    have hc := curvature_mul_le hu0 cutoff_le (cutoff_square_mul_le hlam)
    have hu : rigidityCutoff lam ≤ 13 / 100 := cutoff_le
    nlinarith

/-- The scalar absorption estimate after averaging against a spectral probability law. -/
theorem absorption_for_law (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ → ℝ)
    (hneg : ∀ a ≤ 0, 1 / (7 + a ^ 2) ≤ p a)
    (hpos : ∀ a, 0 ≤ a → 1 / 4 ≤ p a)
    (htail : ∀ a, 4 ≤ a → 23 / 50 ≤ p a)
    (hp : Integrable p μ) (hfirst : Integrable (fun a : ℝ => a) μ)
    (hsecond : Integrable (fun a : ℝ => a ^ 2) μ)
    (hmean : ∫ a, a ∂μ = 0) {lam r : ℝ} (hlam : 0 ≤ lam) (hr : 0 ≤ r)
    (hmoment : ∫ a, a ^ 2 ∂μ = lam + r) :
    Submission.Lib.ScalarLog.dualScale lam - 1 - Real.log (Submission.Lib.ScalarLog.dualScale lam) -
      absorptionFactor lam * (∫ a, p a ∂μ) ≤ (27 / 1000) * r - rigidityWeight lam / 1000 := by
  have hlog := Submission.Lib.ScalarLog.dual_log_le_weight hlam
  have hmeanbound := integral_lower_bound_cutoff μ p hneg hpos htail hp hfirst hsecond hmean hlam hmoment
  have hprod := mul_le_mul_of_nonneg_left hmeanbound (absorptionFactor_nonneg hlam)
  have hloss := mul_le_mul_of_nonneg_right (factor_curvature_le hlam) hr
  have hw : rigidityWeight lam = absorptionFactor lam * rigidityCutoff lam := rfl
  rw [hw] at hlog ⊢
  nlinarith

/-- The pointwise `.111` bound for the terms quadratic in the higher-chaos field. -/
theorem y_cost_le {b h p : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ 1 / 2) (hp : 0 < p)
    (hh : h ^ 2 ≤ (67 / 100 : ℝ) ^ 2 * p) :
    (40 / 37 : ℝ) * ((b - 7 / 25) ^ 2 + (5 / 96) * h ^ 2 / p) ≤ 111 / 1000 := by
  have hs : (b - 7 / 25) ^ 2 ≤ (7 / 25 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hb)]
  have hratio : h ^ 2 / p ≤ (67 / 100 : ℝ) ^ 2 := (div_le_iff₀ hp).mpr hh
  have he : (5 / 96 : ℝ) * h ^ 2 / p = (5 / 96) * (h ^ 2 / p) := by ring
  rw [he]
  nlinarith

end Submission.Obl.Root.ScalarMinorant
