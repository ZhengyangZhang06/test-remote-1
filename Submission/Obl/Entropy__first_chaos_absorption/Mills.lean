import Submission.Lib.GaussianTransport.GaussianTails

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology

namespace Submission.Obl.Entropy__first_chaos_absorption

set_option backward.isDefEq.respectTransparency false

open Submission.Lib.GaussianTransport

private lemma nonneg_of_decreasing_to_zero {F d : ℝ → ℝ}
    (hder : ∀ x, 0 < x → HasDerivAt F (d x) x)
    (hd : ∀ x, 0 < x → d x ≤ 0) (ht : Tendsto F atTop (𝓝 0))
    {r : ℝ} (hr : 0 < r) : 0 ≤ F r := by
  have hc : ContinuousOn F (Ioi 0) := fun x hx => (hder x hx).continuousAt.continuousWithinAt
  have hm : AntitoneOn F (Ioi 0) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0) hc
      (fun x hx => (hder x (by simpa using hx)).hasDerivWithinAt)
      (fun x hx => hd x (by simpa using hx))
  apply le_of_tendsto ht
  filter_upwards [eventually_ge_atTop r] with x hx
  exact hm hr (hr.trans_le hx) hx

private lemma nonpos_of_increasing_to_zero {F d : ℝ → ℝ}
    (hder : ∀ x, 0 < x → HasDerivAt F (d x) x)
    (hd : ∀ x, 0 < x → 0 ≤ d x) (ht : Tendsto F atTop (𝓝 0))
    {r : ℝ} (hr : 0 < r) : F r ≤ 0 := by
  have h := nonneg_of_decreasing_to_zero (F := fun x => -F x) (d := fun x => -d x)
    (fun x hx => (hder x hx).neg) (fun x hx => neg_nonpos.mpr (hd x hx))
    (by simpa only [neg_zero] using ht.neg) hr
  linarith

private lemma tail_deriv (r : ℝ) :
    HasDerivAt (fun x => normalCDF (-x)) (-normalPDF r) r := by
  simpa only [normalPDF_neg, mul_neg_one, Function.comp_def] using
    (hasDerivAt_normalCDF (-r)).comp r (hasDerivAt_neg' r)

private lemma tail_tendsto : Tendsto (fun x => normalCDF (-x)) atTop (𝓝 0) :=
  (tendsto_cdf_atBot (gaussianReal 0 1)).comp tendsto_neg_atTop_atBot

/-- The first lower alternating Mills bound. -/
lemma mills_lower_one {r : ℝ} (hr : 0 < r) :
    r⁻¹ - (r⁻¹)^3 ≤ normalCDF (-r) / normalPDF r := by
  let F : ℝ → ℝ := fun x => normalPDF x * (x⁻¹ - (x⁻¹)^3) - normalCDF (-x)
  have hder (x : ℝ) (hx : 0 < x) : HasDerivAt F (3*normalPDF x / x^4) x := by
    convert! ((hasDerivAt_normalPDF x).mul
      ((hasDerivAt_inv hx.ne').sub ((hasDerivAt_inv hx.ne').pow 3))).sub (tail_deriv x) using 1
    simp only [Pi.sub_apply, Pi.pow_apply]
    simp only [inv_pow]
    field_simp [hx.ne']
    ring
  have ht : Tendsto F atTop (𝓝 0) := by
    have hi : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa [F] using
      (tendsto_normalPDF_atTop.mul (hi.sub (hi.pow 3))).sub tail_tendsto
  have h := nonpos_of_increasing_to_zero hder (fun x hx => by have := (normalPDF_pos x).le; positivity) ht hr
  apply (le_div_iff₀ (normalPDF_pos r)).mpr
  dsimp [F] at h
  linarith

/-- The three-term upper alternating Mills bound. -/
lemma mills_upper_two {r : ℝ} (hr : 0 < r) :
    normalCDF (-r) / normalPDF r ≤ r⁻¹ - (r⁻¹)^3 + 3*(r⁻¹)^5 := by
  let F : ℝ → ℝ := fun x => normalPDF x * (x⁻¹ - (x⁻¹)^3 + 3*(x⁻¹)^5) - normalCDF (-x)
  have hder (x : ℝ) (hx : 0 < x) : HasDerivAt F (-15*normalPDF x / x^6) x := by
    convert! ((hasDerivAt_normalPDF x).mul
      (((hasDerivAt_inv hx.ne').sub ((hasDerivAt_inv hx.ne').pow 3)).add
        (((hasDerivAt_inv hx.ne').pow 5).const_mul 3))).sub (tail_deriv x) using 1
    simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply]
    simp only [inv_pow]
    field_simp [hx.ne']
    ring
  have ht : Tendsto F atTop (𝓝 0) := by
    have hi : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa [F] using
      (tendsto_normalPDF_atTop.mul ((hi.sub (hi.pow 3)).add ((hi.pow 5).const_mul 3))).sub tail_tendsto
  have h := nonneg_of_decreasing_to_zero hder
    (fun x hx => div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (normalPDF_pos x).le) (by positivity)) ht hr
  apply (div_le_iff₀ (normalPDF_pos r)).mpr
  dsimp [F] at h
  linarith

/-- The four-term lower alternating Mills bound. -/
lemma mills_lower_three {r : ℝ} (hr : 0 < r) :
    r⁻¹ - (r⁻¹)^3 + 3*(r⁻¹)^5 - 15*(r⁻¹)^7 ≤ normalCDF (-r) / normalPDF r := by
  let F : ℝ → ℝ := fun x => normalPDF x *
    (x⁻¹ - (x⁻¹)^3 + 3*(x⁻¹)^5 - 15*(x⁻¹)^7) - normalCDF (-x)
  have hder (x : ℝ) (hx : 0 < x) : HasDerivAt F (105*normalPDF x / x^8) x := by
    convert! ((hasDerivAt_normalPDF x).mul
      ((((hasDerivAt_inv hx.ne').sub ((hasDerivAt_inv hx.ne').pow 3)).add
        (((hasDerivAt_inv hx.ne').pow 5).const_mul 3)).sub
        (((hasDerivAt_inv hx.ne').pow 7).const_mul 15))).sub (tail_deriv x) using 1
    simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply]
    simp only [inv_pow]
    field_simp [hx.ne']
    ring
  have ht : Tendsto F atTop (𝓝 0) := by
    have hi : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa [F] using
      (tendsto_normalPDF_atTop.mul (((hi.sub (hi.pow 3)).add ((hi.pow 5).const_mul 3)).sub
        ((hi.pow 7).const_mul 15))).sub tail_tendsto
  have h := nonpos_of_increasing_to_zero hder (fun x hx => by have := (normalPDF_pos x).le; positivity) ht hr
  apply (le_div_iff₀ (normalPDF_pos r)).mpr
  dsimp [F] at h
  linarith

end Submission.Obl.Entropy__first_chaos_absorption
