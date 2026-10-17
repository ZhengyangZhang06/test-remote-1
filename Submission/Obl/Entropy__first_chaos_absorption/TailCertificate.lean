import Submission.Obl.Entropy__first_chaos_absorption.TailRatio
import Submission.Obl.Entropy__first_chaos_absorption.DensityTail
import Submission.Obl.Entropy__first_chaos_absorption.TailAlgebra
import Submission.Obl.Entropy__first_chaos_absorption.NegativeTail
import Submission.Obl.Entropy__first_chaos_absorption.Functions

open MeasureTheory ProbabilityTheory

namespace Submission.Obl.Entropy__first_chaos_absorption

set_option backward.isDefEq.respectTransparency false

open Submission.Lib.GaussianTransport

lemma negative_tail_normalized {r : ℝ} (hr : 6 ≤ r) :
    let u := (r⁻¹)^2
    let K := r*transportRatio (-r)
    let L := r^3*transportCurvature (-r)
    0 ≤ K ∧ K ≤ 1+u/100 ∧ 0 ≤ L ∧ L ≤ 21/10 ∧
      u*(1-(301/100)*u) ≤ transportSlope (-r) ∧
      transportSlope (-r) ≤ u*(1+u/100) := by
  let u := (r⁻¹)^2
  let J := r*(normalCDF (-r)/normalPDF r)
  let K := r*transportRatio (-r)
  let Q := gaussianHazard (-r)/r
  let L := r^3*transportCurvature (-r)
  have hr0 : 0 < r := by linarith
  have hu : 0 < u := sq_pos_of_pos (inv_pos.mpr hr0)
  have hu' : u ≤ 1/36 := by
    have hi : r⁻¹ ≤ (1/6 : ℝ) := (inv_le_comm₀ hr0 (by norm_num)).mpr (by simpa using hr)
    dsimp [u]
    nlinarith [inv_pos.mpr hr0]
  have hJ1 : 1-u ≤ J := by
    convert! mul_le_mul_of_nonneg_left (mills_lower_one hr0) hr0.le using 1
    simp only [u, inv_pow]
    field_simp [hr0.ne']
  have hJ2 : J ≤ 1-u+3*u^2 := by
    convert! mul_le_mul_of_nonneg_left (mills_upper_two hr0) hr0.le using 1
    simp only [u, inv_pow]
    field_simp [hr0.ne']
  have hJ3 : 1-u+3*u^2-15*u^3 ≤ J := by
    convert! mul_le_mul_of_nonneg_left (mills_lower_three hr0) hr0.le using 1
    simp only [u, inv_pow]
    field_simp [hr0.ne']
  have hJ0 : J ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (mills_upper_zero hr0) hr0.le
    simpa [J, hr0.ne'] using hh
  have hk := transportRatio_tail_error hr0
  have hK : 0 ≤ K := by
    apply mul_nonneg hr0.le
    have hh := (transportRatio_mills_bounds r).1
    exact le_trans (mul_nonneg (by linarith [normalCDF_lt_one (-r)])
      (div_nonneg (normalCDF_pos _).le (normalPDF_pos _).le)) hh
  have hKhi : K ≤ J := mul_le_mul_of_nonneg_left hk.2 hr0.le
  have hsmall : normalPDF r/r ≤ u^3/1000 := by
    have hh := mul_le_mul_of_nonneg_right (normalPDF_mul_fifth_small hr)
      (show 0 ≤ (r⁻¹)^6 by positivity)
    convert! hh using 1 <;> simp only [u, inv_pow] <;> field_simp [hr0.ne']
  have hKlo : J-u^3/1000 ≤ K := by
    have hh : J-normalPDF r/r ≤ K := by
      convert! mul_le_mul_of_nonneg_left hk.1 hr0.le using 1
      simp only [J, inv_pow]
      field_simp [hr0.ne']
    linarith
  have hQ : 0 ≤ Q := div_nonneg (gaussianHazard_pos _).le hr0.le
  have hCDF0 : normalCDF 0 = 1/2 := by
    have hh := normalCDF_add_neg 0
    norm_num at hh
    linarith
  have hCDF : 1/2 ≤ normalCDF r := by
    rw [← hCDF0]
    exact monotone_cdf (gaussianReal 0 1) hr0.le
  have hq : gaussianHazard (-r) ≤ 2*normalPDF r := by
    simp only [gaussianHazard, normalPDF_neg, neg_neg]
    apply (div_le_iff₀ (normalCDF_pos r)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hCDF (normalPDF_pos r).le]
  have hQhi : Q ≤ u^3/500 := by
    have hh := div_le_div_of_nonneg_right hq hr0.le
    rw [mul_div_assoc] at hh
    dsimp [Q]
    linarith
  have hb : transportSlope (-r) = 1-K*(1+Q) := by
    dsimp [transportSlope, gaussianGap, K, Q]
    field_simp [hr0.ne'] <;> ring
  have hL : u^2*L = K*(1+u)-1+(K-1)*Q := by
    dsimp [u, L, K, Q, transportCurvature, transportSlope, gaussianGap]
    field_simp [hr0.ne'] <;> ring
  exact ⟨hK, normalized_tail_moments hu hu' hJ1 hJ2 hJ3 hJ0 hK hKlo hKhi hQ hQhi hb hL⟩

/-- Both scalar certificates of Proposition 3.5 on the entire negative tail. -/
theorem negative_tail_certificates {a : ℝ} (ha : a ≤ -6) :
    1/(7+a^2) ≤ pValue a ∧ hValue a^2 ≤ (67/100)^2*pValue a := by
  let r := -a
  have hr : 6 ≤ r := by dsimp [r]; linarith
  have hr0 : 0 < r := by linarith
  let u := (r⁻¹)^2
  let K := r*transportRatio (-r)
  let L := r^3*transportCurvature (-r)
  have hu : 0 ≤ u := sq_nonneg _
  have hu' : u ≤ 1/36 := by
    have hi : r⁻¹ ≤ (1/6 : ℝ) := (inv_le_comm₀ hr0 (by norm_num)).mpr (by simpa using hr)
    dsimp [u]
    nlinarith [inv_pos.mpr hr0]
  obtain ⟨hK, hK', hL, hL', hb, hb'⟩ := negative_tail_normalized hr
  have hh := negative_tail_algebra_wide hu hu' hK hK' hL hL' hb hb'
  have hp : transportSlope (-r)+K*L*u^2-(40/3)*L^2*u^3 = pValue a := by
    dsimp [K, L, u, pValue]
    simp only [show -r = a by dsimp [r]; ring]
    field_simp [hr0.ne']
  have hhh : u*(K*(transportSlope (-r)-1/2)-(80/3)*(transportSlope (-r)-7/25)*L*u)^2 =
      hValue a^2 := by
    dsimp [K, L, u, hValue]
    simp only [show -r = a by dsimp [r]; ring]
    field_simp [hr0.ne']
  have huform : u/(1+7*u) = 1/(7+a^2) := by
    dsimp [u]
    field_simp [hr0.ne']
    dsimp [r]
    ring
  change u/(1+7*u) ≤ transportSlope (-r)+K*L*u^2-(40/3)*L^2*u^3 ∧
    u*(K*(transportSlope (-r)-1/2)-(80/3)*(transportSlope (-r)-7/25)*L*u)^2 ≤
      (67/100)^2*(transportSlope (-r)+K*L*u^2-(40/3)*L^2*u^3) at hh
  simpa only [hp, hhh, huform] using hh

end Submission.Obl.Entropy__first_chaos_absorption
