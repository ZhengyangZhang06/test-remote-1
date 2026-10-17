/-
Adapted from: here:root
Original proofs by session x0014 using a positive Gaussian tail moment determinant:
strict transport curvature, excess variance ratio, and scalar reserve growth.
-/

import Submission.Lib.GaussianTransport.GaussianSlope
import Submission.Lib.GaussianCurvature.LogHazardCoordinates

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Lib.GaussianCurvature

open Submission.Lib.GaussianTransport

/-- Gaussian integration by parts gives every polynomial tail moment recursively. -/
theorem integral_pow_succ_succ_tail (a : ℝ) (n : ℕ) :
    (∫ x in Ioi a, x ^ (n + 2) * normalPDF x) =
      a ^ (n + 1) * normalPDF a + (n + 1 : ℝ) * ∫ x in Ioi a, x ^ n * normalPDF x := by
  have hd (x : ℝ) : HasDerivAt (fun x => x ^ (n + 1) * normalPDF x)
      ((n + 1 : ℝ) * (x ^ n * normalPDF x) - x ^ (n + 2) * normalPDF x) x := by
    have h := ((hasDerivAt_id x).pow (n + 1)).mul (hasDerivAt_normalPDF x)
    change HasDerivAt (fun x => x ^ (n + 1) * normalPDF x) _ x at h
    apply h.congr_deriv
    simp only [Pi.pow_apply, id_eq, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    simp only [pow_succ]
    ring
  have hi := ((integrable_pow_mul_normalPDF n).const_mul (n + 1 : ℝ)).sub
    (integrable_pow_mul_normalPDF (n + 2))
  have ht : Tendsto (fun x => x ^ (n + 1) * normalPDF x) atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0) (fun x _ => hd x)
      hi.integrableOn (integrable_pow_mul_normalPDF (n + 1)).integrableOn
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x)
    hi.integrableOn ht (a := a)
  rw [integral_sub ((integrable_pow_mul_normalPDF n).const_mul (n + 1 : ℝ)).integrableOn
    (integrable_pow_mul_normalPDF (n + 2)).integrableOn, integral_const_mul] at h
  linarith

theorem integral_cube_tail (a : ℝ) :
    (∫ x in Ioi a, x ^ 3 * normalPDF x) = (a ^ 2 + 2) * normalPDF a := by
  have h := integral_pow_succ_succ_tail a 1
  norm_num only [Nat.cast_one, Nat.reduceAdd, one_add_one_eq_two, pow_one] at h
  rw [integral_mul_normalPDF_tail] at h
  linarith

theorem integral_fourth_tail (a : ℝ) :
    (∫ x in Ioi a, x ^ 4 * normalPDF x) =
      (a ^ 3 + 3 * a) * normalPDF a + 3 * normalCDF (-a) := by
  have h := integral_pow_succ_succ_tail a 2
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at h
  rw [integral_sq_mul_normalPDF_tail] at h
  linarith

theorem integrable_quadratic_sq (c b : ℝ) :
    Integrable (fun x : ℝ => (x ^ 2 - c * x - b) ^ 2 * normalPDF x) := by
  have hp : Integrable normalPDF := integrable_gaussianPDFReal 0 1
  have h1 : Integrable (fun x => x * normalPDF x) := by
    simpa only [pow_one] using integrable_pow_mul_normalPDF 1
  have h := ((((integrable_pow_mul_normalPDF 4).add
    ((integrable_pow_mul_normalPDF 3).const_mul (-2 * c))).add
    ((integrable_pow_mul_normalPDF 2).const_mul (c ^ 2 - 2 * b))).add
    (h1.const_mul (2 * c * b))).add (hp.const_mul (b ^ 2))
  convert! h using 1
  funext x
  simp only [Pi.add_apply]
  ring

/-- No monic quadratic vanishes almost everywhere on a Gaussian tail. -/
theorem integral_quadratic_sq_pos (a c b : ℝ) :
    0 < ∫ x in Ioi a, (x ^ 2 - c * x - b) ^ 2 * normalPDF x := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (fun x => mul_nonneg (sq_nonneg _) (normalPDF_pos x).le))
    (integrable_quadratic_sq c b).integrableOn).2
  have hs : Ioi (max a (|c| + |b| + 2)) ⊆
      Function.support (fun x => (x ^ 2 - c * x - b) ^ 2 * normalPDF x) ∩ Ioi a := by
    intro x hx
    have ha : a < x := (le_max_left _ _).trans_lt hx
    have hx' : |c| + |b| + 2 < x := (le_max_right _ _).trans_lt hx
    have hx0 : 0 < x := by linarith [abs_nonneg c, abs_nonneg b]
    have hcx := mul_le_mul_of_nonneg_right (le_abs_self c) hx0.le
    have hprod : 0 < x * (x - |c| - 1) := mul_pos hx0 (by linarith [abs_nonneg b])
    have hpoly : 0 < x ^ 2 - c * x - b := by
      nlinarith [le_abs_self b, abs_nonneg c]
    exact ⟨mul_ne_zero (pow_ne_zero _ hpoly.ne') (normalPDF_pos x).ne', ha⟩
  have hmeasure := measure_mono (μ := volume) hs
  rw [Real.volume_Ioi] at hmeasure
  exact ENNReal.zero_lt_top.trans_le hmeasure

theorem integral_quadratic_sq_tail (a c b : ℝ) :
    (∫ x in Ioi a, (x ^ 2 - c * x - b) ^ 2 * normalPDF x) =
      (a ^ 3 + 3 * a) * normalPDF a + 3 * normalCDF (-a) +
      (-2 * c) * ((a ^ 2 + 2) * normalPDF a) +
      (c ^ 2 - 2 * b) * (a * normalPDF a + normalCDF (-a)) +
      (2 * c * b) * normalPDF a + b ^ 2 * normalCDF (-a) := by
  have hp : Integrable normalPDF := integrable_gaussianPDFReal 0 1
  have h1 : Integrable (fun x => x * normalPDF x) := by
    simpa only [pow_one] using integrable_pow_mul_normalPDF 1
  have h4 := (integrable_pow_mul_normalPDF 4).integrableOn (s := Ioi a)
  have h3 := ((integrable_pow_mul_normalPDF 3).const_mul (-2 * c)).integrableOn (s := Ioi a)
  have h2 := ((integrable_pow_mul_normalPDF 2).const_mul (c ^ 2 - 2 * b)).integrableOn (s := Ioi a)
  have h1' := (h1.const_mul (2 * c * b)).integrableOn (s := Ioi a)
  have h0 := (hp.const_mul (b ^ 2)).integrableOn (s := Ioi a)
  have heq (x : ℝ) : (x ^ 2 - c * x - b) ^ 2 * normalPDF x =
      x ^ 4 * normalPDF x + (-2 * c) * (x ^ 3 * normalPDF x) +
      (c ^ 2 - 2 * b) * (x ^ 2 * normalPDF x) +
      (2 * c * b) * (x * normalPDF x) + b ^ 2 * normalPDF x := by ring
  simp_rw [heq]
  have hs4 := integral_add (((h4.add h3).add h2).add h1') h0
  have hs3 := integral_add ((h4.add h3).add h2) h1'
  have hs2 := integral_add (h4.add h3) h2
  have hs1 := integral_add h4 h3
  simp only [Pi.add_apply] at hs4 hs3 hs2 hs1
  rw [hs4, hs3, hs2, hs1]
  simp only [integral_const_mul, integral_fourth_tail, integral_cube_tail,
    integral_sq_mul_normalPDF_tail, integral_mul_normalPDF_tail, ← normalCDF_neg_eq_tail]

/-- Strict positivity of the degree-two Gaussian tail moment determinant. -/
theorem tail_moment_determinant_pos (a : ℝ) :
    0 < (1 - a * gaussianGap a) * (2 - a * gaussianGap a) -
      gaussianGap a ^ 2 * (3 - a * gaussianGap a) := by
  let q := gaussianHazard a
  let r := 1 + a * q
  let v := r - q ^ 2
  have hv : 0 < v := by
    have h := one_sub_hazard_mul_gap_pos a
    dsimp [v, r, q]
    unfold gaussianGap at h
    nlinarith
  let c := ((a ^ 2 + 2) * q - q * r) / v
  let b := r - c * q
  have hp := mul_pos (integral_quadratic_sq_pos a c b) hv
  have hpdf : normalPDF a = q * normalCDF (-a) := by
    dsimp [q, gaussianHazard]
    field_simp [(normalCDF_pos (-a)).ne']
  have hv0 : 1 + a * q - q ^ 2 ≠ 0 := hv.ne'
  have heq :
      (∫ x in Ioi a, (x ^ 2 - c * x - b) ^ 2 * normalPDF x) * v =
        normalCDF (-a) *
          ((1 - a * (q - a)) * (2 - a * (q - a)) - (q - a) ^ 2 * (3 - a * (q - a))) := by
    rw [integral_quadratic_sq_tail, hpdf]
    dsimp only [c, b, v, r]
    field_simp [hv0]
    ring
  rw [heq] at hp
  exact (mul_pos_iff_of_pos_left (normalCDF_pos (-a))).mp hp

theorem excess_second_moment_pos (a : ℝ) : 0 < 1 - a * gaussianGap a := by
  have h := one_sub_hazard_mul_gap_pos a
  have hd := gaussianGap_pos a
  unfold gaussianGap at *
  nlinarith

/-- The comparison whose derivative is the positive tail moment determinant. -/
noncomputable def curvatureComparison (a : ℝ) : ℝ :=
  exponentialTransport a - gaussianHazard a * gaussianGap a / (1 - a * gaussianGap a)

theorem hasDerivAt_curvatureComparison (a : ℝ) :
    HasDerivAt curvatureComparison
      (gaussianHazard a *
        ((1 - a * gaussianGap a) * (2 - a * gaussianGap a) -
          gaussianGap a ^ 2 * (3 - a * gaussianGap a)) / (1 - a * gaussianGap a) ^ 2) a := by
  have hd := ((hasDerivAt_id a).mul (hasDerivAt_gaussianGap a)).const_sub 1
  have hr := ((hasDerivAt_gaussianHazard a).mul (hasDerivAt_gaussianGap a)).div hd
    (excess_second_moment_pos a).ne'
  have h := (hasDerivAt_exponentialTransport a).sub hr
  change HasDerivAt curvatureComparison _ a at h
  apply h.congr_deriv
  dsimp
  field_simp [(excess_second_moment_pos a).ne']
  unfold gaussianGap
  ring

theorem tendsto_curvatureComparison_atBot : Tendsto curvatureComparison atBot (𝓝 0) := by
  have hgap : Tendsto gaussianGap atBot atTop := by
    apply tendsto_atTop_mono (f := fun a : ℝ => -a) _ tendsto_neg_atBot_atTop
    intro a
    have h := gaussianHazard_pos a
    dsimp only [gaussianGap]
    linarith
  have hqdiv := tendsto_gaussianHazard_atBot.div_atTop hgap
  have hR : Tendsto (fun a => gaussianHazard a * gaussianGap a / (1 - a * gaussianGap a))
      atBot (𝓝 0) := by
    apply squeeze_zero _ _ hqdiv
    · intro a
      exact div_nonneg (mul_nonneg (gaussianHazard_pos a).le (gaussianGap_pos a).le)
        (excess_second_moment_pos a).le
    · intro a
      rw [div_le_div_iff₀ (excess_second_moment_pos a) (gaussianGap_pos a)]
      have hv := one_sub_hazard_mul_gap_pos a
      have hq := gaussianHazard_pos a
      have hd : gaussianGap a ^ 2 ≤ 1 - a * gaussianGap a := by
        unfold gaussianGap at *
        nlinarith
      have h := mul_le_mul_of_nonneg_left hd hq.le
      nlinarith
  have hc : Tendsto (fun a => normalCDF (-a)) atBot (𝓝 1) :=
    (tendsto_cdf_atTop (gaussianReal 0 1)).comp tendsto_neg_atBot_atTop
  have ht : Tendsto exponentialTransport atBot (𝓝 0) := by
    change Tendsto (fun a => -Real.log (normalCDF (-a))) atBot (𝓝 0)
    simpa only [Real.log_one, neg_zero] using (hc.log one_ne_zero).neg
  change Tendsto (fun a => exponentialTransport a -
    gaussianHazard a * gaussianGap a / (1 - a * gaussianGap a)) atBot (𝓝 0)
  simpa only [sub_zero] using ht.sub hR

/-- The transport ratio is strictly convex: the second scalar positivity assertion
in Lemma 2.2 follows from a Gaussian moment determinant, without numerical estimates. -/
theorem transportCurvature_pos (a : ℝ) : 0 < transportCurvature a := by
  have hm : StrictMono curvatureComparison := by
    apply strictMono_of_hasDerivAt_pos hasDerivAt_curvatureComparison
    intro x
    exact div_pos (mul_pos (gaussianHazard_pos x) (tail_moment_determinant_pos x))
      (sq_pos_of_pos (excess_second_moment_pos x))
  have hn := hm.monotone.le_of_tendsto tendsto_curvatureComparison_atBot (a - 1)
  have hlt := hm (show a - 1 < a by linarith)
  have hcmp : 0 < curvatureComparison a := lt_of_le_of_lt hn hlt
  unfold curvatureComparison at hcmp
  have hnum := (div_lt_iff₀ (excess_second_moment_pos a)).mp (sub_pos.mp hcmp)
  have heq : gaussianHazard a * transportCurvature a =
      exponentialTransport a * (1 - a * gaussianGap a) - gaussianHazard a * gaussianGap a := by
    unfold transportCurvature transportSlope transportRatio
    field_simp [(gaussianHazard_pos a).ne']
    unfold gaussianGap
    ring
  apply (mul_pos_iff_of_pos_left (gaussianHazard_pos a)).mp
  rw [heq]
  linarith

/-- The scalar transport slope is strictly increasing. -/
theorem strictMono_transportSlope : StrictMono transportSlope :=
  strictMono_of_hasDerivAt_pos hasDerivAt_transportSlope transportCurvature_pos

/-- The variance divided by the squared mean for the positive Gaussian excess. -/
noncomputable def excessVarianceRatio (a : ℝ) : ℝ :=
  (1 - gaussianHazard a * gaussianGap a) / gaussianGap a ^ 2

theorem hasDerivAt_excessVarianceRatio (a : ℝ) :
    HasDerivAt excessVarianceRatio
      (((1 - a * gaussianGap a) * (2 - a * gaussianGap a) -
        gaussianGap a ^ 2 * (3 - a * gaussianGap a)) / gaussianGap a ^ 3) a := by
  have h := (((hasDerivAt_gaussianHazard a).mul (hasDerivAt_gaussianGap a)).const_sub 1).div
    ((hasDerivAt_gaussianGap a).pow 2) (pow_ne_zero 2 (gaussianGap_pos a).ne')
  change HasDerivAt excessVarianceRatio _ a at h
  apply h.congr_deriv
  dsimp
  field_simp [(gaussianGap_pos a).ne']
  unfold gaussianGap
  ring

/-- Strict growth of the excess variance-to-mean-square ratio. -/
theorem strictMono_excessVarianceRatio : StrictMono excessVarianceRatio := by
  apply strictMono_of_hasDerivAt_pos hasDerivAt_excessVarianceRatio
  intro a
  exact div_pos (tail_moment_determinant_pos a) (pow_pos (gaussianGap_pos a) 3)

/-- The scalar identities express `l` without differentiating a quotient. -/
theorem curvature_identity (a : ℝ) :
    transportCurvature a = transportRatio a * (1 - gaussianHazard a * gaussianGap a) -
      transportSlope a * gaussianGap a := by
  unfold transportCurvature transportSlope transportRatio gaussianGap
  field_simp [(gaussianHazard_pos a).ne']
  ring

/-- A positive decomposition of the logarithmic growth of `M=d⁻²(1-b²)`. -/
theorem log_M_growth_eq (a : ℝ) :
    2 * (1 - gaussianHazard a * gaussianGap a) / gaussianGap a ^ 2 -
      2 * transportSlope a * transportCurvature a /
        (gaussianGap a * (1 - transportSlope a ^ 2)) =
      transportSlope a / (1 - transportSlope a) +
        transportCurvature a / (gaussianGap a * (1 + transportSlope a)) +
        excessVarianceRatio a := by
  have hb := transportSlope_pos a
  have hbhalf := transportSlope_lt_half a
  have hd := gaussianGap_pos a
  have hb1 : 0 < 1 - transportSlope a := by linarith
  have hbp : 0 < 1 + transportSlope a := by linarith
  have hbs : 0 < 1 - transportSlope a ^ 2 := by nlinarith
  have hkd : transportRatio a * gaussianGap a = 1 - transportSlope a := by
    unfold transportSlope
    ring
  have hlform : transportCurvature a =
      ((1 - transportSlope a) * (1 - gaussianHazard a * gaussianGap a) -
        transportSlope a * gaussianGap a ^ 2) / gaussianGap a := by
    apply (eq_div_iff hd.ne').2
    rw [curvature_identity]
    calc
      _ = (transportRatio a * gaussianGap a) * (1 - gaussianHazard a * gaussianGap a) -
          transportSlope a * gaussianGap a ^ 2 := by ring
      _ = _ := by rw [hkd]
  rw [hlform]
  unfold excessVarianceRatio
  field_simp [hd.ne', hb1.ne', hbp.ne', hbs.ne']
  ring

/-- The logarithmic growth rate of `M=d⁻²(1-b²)` is positive on the whole real line. -/
theorem log_M_growth_pos (a : ℝ) :
    0 < 2 * (1 - gaussianHazard a * gaussianGap a) / gaussianGap a ^ 2 -
      2 * transportSlope a * transportCurvature a /
        (gaussianGap a * (1 - transportSlope a ^ 2)) := by
  rw [log_M_growth_eq]
  have hb := transportSlope_pos a
  have hbhalf := transportSlope_lt_half a
  have hd := gaussianGap_pos a
  have hl := transportCurvature_pos a
  have hv := one_sub_hazard_mul_gap_pos a
  have hb1 : 0 < 1 - transportSlope a := by linarith
  have hbp : 0 < 1 + transportSlope a := by linarith
  have hR : 0 < excessVarianceRatio a := div_pos hv (sq_pos_of_pos hd)
  exact add_pos (add_pos (div_pos hb hb1) (div_pos hl (mul_pos hd hbp))) hR

/-- The growth rate depends only on the increasing quantities `b` and `Var(X)/E(X)²`. -/
theorem log_M_growth_eq_ratios (a : ℝ) :
    2 * (1 - gaussianHazard a * gaussianGap a) / gaussianGap a ^ 2 -
      2 * transportSlope a * transportCurvature a /
        (gaussianGap a * (1 - transportSlope a ^ 2)) =
      2 * (excessVarianceRatio a + transportSlope a ^ 2 / (1 - transportSlope a)) /
        (1 + transportSlope a) := by
  rw [log_M_growth_eq, curvature_identity]
  have hb := transportSlope_pos a
  have hbhalf := transportSlope_lt_half a
  have hd := gaussianGap_pos a
  have hb1 : 1 - transportSlope a ≠ 0 := by linarith
  have hbp : 1 + transportSlope a ≠ 0 := by linarith
  have hkd : transportRatio a = (1 - transportSlope a) / gaussianGap a := by
    apply (eq_div_iff hd.ne').2
    unfold transportSlope
    ring
  rw [hkd]
  unfold excessVarianceRatio
  field_simp [hd.ne', hb1, hbp]
  ring

/-- Bounds for the two increasing ratios give an interval-wide growth bound. -/
theorem log_M_growth_lower_bound (a blo bhi rlo : ℝ)
    (hbl0 : 0 ≤ blo) (hbl : blo ≤ transportSlope a)
    (hbu : transportSlope a ≤ bhi) (hr0 : 0 ≤ rlo)
    (hr : rlo ≤ excessVarianceRatio a) :
    2 * (rlo + blo ^ 2 / (1 - blo)) / (1 + bhi) ≤
      2 * (1 - gaussianHazard a * gaussianGap a) / gaussianGap a ^ 2 -
        2 * transportSlope a * transportCurvature a /
          (gaussianGap a * (1 - transportSlope a ^ 2)) := by
  rw [log_M_growth_eq_ratios]
  have hb := transportSlope_pos a
  have hbhalf := transportSlope_lt_half a
  have hden : 0 < 1 - transportSlope a := by linarith
  have hlo : 0 < 1 - blo := by linarith
  have hsq : blo ^ 2 ≤ transportSlope a ^ 2 := by nlinarith
  have hterm : blo ^ 2 / (1 - blo) ≤ transportSlope a ^ 2 / (1 - transportSlope a) :=
    (div_le_div_of_nonneg_left (sq_nonneg blo) hden (by linarith)).trans
      (div_le_div_of_nonneg_right hsq hden.le)
  have hn : 0 ≤ 2 * (rlo + blo ^ 2 / (1 - blo)) := by positivity
  calc
    _ ≤ 2 * (rlo + blo ^ 2 / (1 - blo)) / (1 + transportSlope a) :=
      div_le_div_of_nonneg_left hn (by linarith) (by linarith)
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add hr hterm) (by norm_num)) (by linarith)

/-- Completing a square gives a growth bound from the variance ratio alone. -/
theorem log_M_growth_lower_bound_of_ratio (a r m : ℝ) (hm : 0 ≤ m)
    (hr : r ≤ excessVarianceRatio a) (hc : r ^ 2 ≤ (2 + m) * (2 * r - m)) :
    m ≤ 2 * (1 - gaussianHazard a * gaussianGap a) / gaussianGap a ^ 2 -
      2 * transportSlope a * transportCurvature a /
        (gaussianGap a * (1 - transportSlope a ^ 2)) := by
  rw [log_M_growth_eq_ratios]
  have hb := transportSlope_pos a
  have hbhalf := transportSlope_lt_half a
  have hden : 0 < 1 - transportSlope a := by linarith
  have hpoly : 0 ≤ (2 + m) * transportSlope a ^ 2 -
      2 * r * transportSlope a + 2 * r - m := by
    have heq : (2 + m) * ((2 + m) * transportSlope a ^ 2 -
        2 * r * transportSlope a + 2 * r - m) =
        ((2 + m) * transportSlope a - r) ^ 2 +
          ((2 + m) * (2 * r - m) - r ^ 2) := by ring
    have hp : 0 ≤ (2 + m) * ((2 + m) * transportSlope a ^ 2 -
        2 * r * transportSlope a + 2 * r - m) := by
      rw [heq]
      exact add_nonneg (sq_nonneg _) (sub_nonneg.mpr hc)
    exact nonneg_of_mul_nonneg_right hp (show 0 < 2 + m by linarith)
  have hR := mul_le_mul_of_nonneg_right hr hden.le
  have hid : excessVarianceRatio a + transportSlope a ^ 2 / (1 - transportSlope a) =
      (excessVarianceRatio a * (1 - transportSlope a) + transportSlope a ^ 2) /
        (1 - transportSlope a) := by
    field_simp [hden.ne']
  rw [le_div_iff₀ (show 0 < 1 + transportSlope a by linarith), hid,
    ← mul_div_assoc, le_div_iff₀ hden]
  nlinarith

/-- A rational hazard upper bound gives a rational lower variance ratio. -/
theorem excessVarianceRatio_ge_of_hazard_le {a q r : ℝ}
    (hr : 0 ≤ r) (hq : gaussianHazard a ≤ q)
    (hc : r * (q - a) ^ 2 + q * (q - a) ≤ 1) :
    r ≤ excessVarianceRatio a := by
  have hd := gaussianGap_pos a
  have hq0 := gaussianHazard_pos a
  have hqd : gaussianGap a ≤ q - a := by dsimp [gaussianGap]; linarith
  have hqd0 : 0 ≤ q - a := hd.le.trans hqd
  have hs : gaussianGap a ^ 2 ≤ (q - a) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hs hr
  have hprod : gaussianHazard a * gaussianGap a ≤ q * (q - a) :=
    mul_le_mul hq hqd hd.le (hq0.le.trans hq)
  unfold excessVarianceRatio
  rw [le_div_iff₀ (sq_pos_of_pos hd)]
  linarith

/-- The first quantitative growth rate follows from one hazard endpoint. -/
theorem log_M_growth_ge_nineteen {a : ℝ} (ha : -3 ≤ a)
    (hq : gaussianHazard (-3) ≤ 1 / 200) :
    (19 / 100 : ℝ) ≤
      2 * (1 - gaussianHazard a * gaussianGap a) / gaussianGap a ^ 2 -
        2 * transportSlope a * transportCurvature a /
          (gaussianGap a * (1 - transportSlope a ^ 2)) := by
  apply log_M_growth_lower_bound_of_ratio a (1 / 10) (19 / 100) (by norm_num)
  · exact (excessVarianceRatio_ge_of_hazard_le (by norm_num) hq (by norm_num)).trans
      (strictMono_excessVarianceRatio.monotone ha)
  · norm_num

/-- The second quantitative growth rate follows from one hazard endpoint. -/
theorem log_M_growth_ge_thirty_eight {a : ℝ} (ha : -2 ≤ a)
    (hq : gaussianHazard (-2) ≤ 7 / 125) :
    (38 / 100 : ℝ) ≤
      2 * (1 - gaussianHazard a * gaussianGap a) / gaussianGap a ^ 2 -
        2 * transportSlope a * transportCurvature a /
          (gaussianGap a * (1 - transportSlope a ^ 2)) := by
  apply log_M_growth_lower_bound_of_ratio a (1 / 5) (38 / 100) (by norm_num)
  · exact (excessVarianceRatio_ge_of_hazard_le (by norm_num) hq (by norm_num)).trans
      (strictMono_excessVarianceRatio.monotone ha)
  · norm_num

/-- The final quantitative growth rate follows from one hazard endpoint. -/
theorem log_M_growth_ge_sixty_eight {a : ℝ} (ha : -1 ≤ a)
    (hq : gaussianHazard (-1) ≤ 59 / 200) :
    (68 / 100 : ℝ) ≤
      2 * (1 - gaussianHazard a * gaussianGap a) / gaussianGap a ^ 2 -
        2 * transportSlope a * transportCurvature a /
          (gaussianGap a * (1 - transportSlope a ^ 2)) := by
  apply log_M_growth_lower_bound_of_ratio a (11 / 30) (68 / 100) (by norm_num)
  · exact (excessVarianceRatio_ge_of_hazard_le (by norm_num) hq (by norm_num)).trans
      (strictMono_excessVarianceRatio.monotone ha)
  · norm_num

/-- The scalar reserve `M=(1-b²)/d²` in the two-eigenvalue comparison. -/
noncomputable def slopeReserve (a : ℝ) : ℝ :=
  (1 - transportSlope a ^ 2) / gaussianGap a ^ 2

theorem slopeReserve_pos (a : ℝ) : 0 < slopeReserve a := by
  have hb := transportSlope_pos a
  have hbhalf := transportSlope_lt_half a
  exact div_pos (by nlinarith) (sq_pos_of_pos (gaussianGap_pos a))

theorem hasDerivAt_slopeReserve (a : ℝ) :
    HasDerivAt slopeReserve
      (gaussianGap a * slopeReserve a *
        (2 * (1 - gaussianHazard a * gaussianGap a) / gaussianGap a ^ 2 -
          2 * transportSlope a * transportCurvature a /
            (gaussianGap a * (1 - transportSlope a ^ 2)))) a := by
  have h := (((hasDerivAt_transportSlope a).pow 2).const_sub 1).div
    ((hasDerivAt_gaussianGap a).pow 2) (pow_ne_zero 2 (gaussianGap_pos a).ne')
  change HasDerivAt slopeReserve _ a at h
  apply h.congr_deriv
  have hb := transportSlope_pos a
  have hbhalf := transportSlope_lt_half a
  have hbs : 1 - transportSlope a ^ 2 ≠ 0 := ne_of_gt (by nlinarith)
  dsimp [slopeReserve]
  field_simp [(gaussianGap_pos a).ne', hbs]
  ring

/-- The scalar reserve increases strictly, without interval certificates. -/
theorem strictMono_slopeReserve : StrictMono slopeReserve := by
  apply strictMono_of_hasDerivAt_pos hasDerivAt_slopeReserve
  intro a
  exact mul_pos (mul_pos (gaussianGap_pos a) (slopeReserve_pos a)) (log_M_growth_pos a)

end Submission.Lib.GaussianCurvature
