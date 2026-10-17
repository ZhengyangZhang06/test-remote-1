/-
Adapted from: here:root
Original arbitrary-order Mills remainder and anchor proofs by session x0023.
-/

import Submission.Lib.ScalarLog.GaussianEndpoints

/-! Arbitrary-order rational Mills bounds by a signed tail remainder. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Lib.ScalarLog

open Submission.Lib.GaussianTransport

/-- The odd double factorial, defined by its recursion. -/
def millsCoefficient : ℕ → ℝ
  | 0 => 1
  | n + 1 => (2 * n + 1 : ℝ) * millsCoefficient n

lemma millsCoefficient_pos (n : ℕ) : 0 < millsCoefficient n := by
  induction n with
  | zero => norm_num [millsCoefficient]
  | succ n ih => simp only [millsCoefficient]; positivity

/-- The alternating tail remainder, with its sign removed. -/
noncomputable def tailRemainder : ℕ → ℝ → ℝ
  | 0, a => normalCDF (-a)
  | n + 1, a => millsCoefficient n * normalPDF a / a ^ (2 * n + 1) - tailRemainder n a

lemma hasDerivAt_tailRemainder (n : ℕ) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (tailRemainder n)
      (-millsCoefficient n * normalPDF a / a ^ (2 * n)) a := by
  induction n with
  | zero =>
      convert! (hasDerivAt_normalCDF (-a)).comp a (hasDerivAt_id a).neg using 1
      simp [millsCoefficient, normalPDF_neg]
  | succ n ih =>
      have hp := ((hasDerivAt_normalPDF a).const_mul (millsCoefficient n)).div
        ((hasDerivAt_id a).pow (2 * n + 1)) (pow_ne_zero _ ha.ne')
      convert! hp.sub ih using 1
      simp only [Pi.pow_apply, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
          Nat.cast_one, id_eq, millsCoefficient]
      simp only [Nat.mul_add, Nat.mul_one, pow_add, pow_one]
      field_simp [ha.ne']
      ring

lemma tendsto_tailRemainder (n : ℕ) : Tendsto (tailRemainder n) atTop (𝓝 0) := by
  induction n with
  | zero => exact (tendsto_cdf_atBot (gaussianReal 0 1)).comp tendsto_neg_atTop_atBot
  | succ n ih =>
      have hp := (tendsto_normalPDF_atTop.const_mul (millsCoefficient n)).div_atTop
        (tendsto_pow_atTop (by omega : 2 * n + 1 ≠ 0))
      convert! hp.sub ih using 1
      simp

/-- Every finite alternating remainder has the expected sign. -/
theorem tailRemainder_nonneg (n : ℕ) {a : ℝ} (ha : 0 < a) : 0 ≤ tailRemainder n a := by
  have hm : AntitoneOn (tailRemainder n) (Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · intro x hx
      exact (hasDerivAt_tailRemainder n hx).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : 0 < x := by simpa using hx
      exact (hasDerivAt_tailRemainder n hx').differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : 0 < x := by simpa using hx
      rw [(hasDerivAt_tailRemainder n hx').deriv]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (millsCoefficient_pos n).le)
          (normalPDF_pos x).le) (pow_nonneg hx'.le _)
  exact le_of_tendsto (tendsto_tailRemainder n)
    (eventually_atTop.2 ⟨a, fun b hab => hm ha (ha.trans_le hab) hab⟩)

/-- A finite alternating Mills expansion. -/
noncomputable def millsApprox : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n + 1, a => millsApprox n a + (-1 : ℝ) ^ n * millsCoefficient n / a ^ (2 * n + 1)

lemma normalCDF_eq_approx_add_remainder (n : ℕ) (a : ℝ) :
    normalCDF (-a) = normalPDF a * millsApprox n a + (-1 : ℝ) ^ n * tailRemainder n a := by
  induction n with
  | zero => simp [millsApprox, tailRemainder]
  | succ n ih =>
      rw [millsApprox, tailRemainder, pow_succ]
      calc
        _ = normalPDF a * millsApprox n a + (-1 : ℝ) ^ n * tailRemainder n a := ih
        _ = _ := by ring

/-- Every even truncation lies below the Mills ratio and every odd one above. -/
theorem mills_bounds (n : ℕ) {a : ℝ} (ha : 0 < a) :
    normalPDF a * millsApprox (2 * n) a ≤ normalCDF (-a) ∧
      normalCDF (-a) ≤ normalPDF a * millsApprox (2 * n + 1) a := by
  have h0 := normalCDF_eq_approx_add_remainder (2 * n) a
  have h1 := normalCDF_eq_approx_add_remainder (2 * n + 1) a
  simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul] at h0 h1
  constructor <;> linarith [tailRemainder_nonneg (2 * n) ha, tailRemainder_nonneg (2 * n + 1) ha]

/-- The nine/ten-term Mills certificate for the positive central anchor. -/
theorem gaussianHazard_ten_anchor :
    |gaussianHazard 10 - (10098093234 : ℝ) / 1000000000| < 1 / 2500000000 := by
  have hlo := (mills_bounds 5 (by norm_num : (0 : ℝ) < 10)).1
  have hup := (mills_bounds 4 (by norm_num : (0 : ℝ) < 10)).2
  norm_num [millsApprox, millsCoefficient] at hlo hup
  have hpdf := normalPDF_pos 10
  have hcdf := normalCDF_pos (-10)
  rw [abs_lt]
  constructor
  · have h : (10098093234 : ℝ) / 1000000000 - 1 / 2500000000 < gaussianHazard 10 := by
      rw [gaussianHazard, lt_div_iff₀ hcdf]
      linarith
    linarith
  · have h : gaussianHazard 10 < (10098093234 : ℝ) / 1000000000 + 1 / 2500000000 := by
      rw [gaussianHazard, div_lt_iff₀ hcdf]
      linarith
    linarith

private theorem normalPDF_six_lt : normalPDF 6 < (1 : ℝ) / 10000000 := by
  have he : (5 : ℝ) / 2 < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he18 : (10000000 : ℝ) < Real.exp 18 := by
    calc
      (10000000 : ℝ) < (5 / 2 : ℝ) ^ 18 := by norm_num
      _ < Real.exp 1 ^ 18 := pow_lt_pow_left₀ he (by norm_num) (by norm_num)
      _ = Real.exp 18 := by norm_num [← Real.exp_nat_mul]
  rw [normalPDF_eq_inv, show (6 : ℝ) ^ 2 / 2 = 18 by norm_num]
  apply (div_lt_iff₀ (mul_pos (Real.sqrt_pos.2 (by positivity)) (Real.exp_pos 18))).2
  nlinarith [mul_lt_mul_of_pos_left he18 (lt_trans (by norm_num) sqrt_two_pi_lower),
    sqrt_two_pi_lower]

/-- The paper's negative central anchor, certified by nine/ten Mills terms. -/
theorem transportRatio_neg_six_anchor :
    |transportRatio (-6) - (16237766 : ℝ) / 100000000| < 1 / 25000000 := by
  have hlo := (mills_bounds 5 (by norm_num : (0 : ℝ) < 6)).1
  have hup := (mills_bounds 4 (by norm_num : (0 : ℝ) < 6)).2
  have hfirst := (mills_bounds 0 (by norm_num : (0 : ℝ) < 6)).2
  norm_num [millsApprox, millsCoefficient] at hlo hup hfirst
  have hphi := normalPDF_pos 6
  have hc := normalCDF_pos 6
  have htail := normalCDF_pos (-6)
  have href := normalCDF_add_neg 6
  have hsmall : 1 - 1 / 10000000 < normalCDF 6 := by
    have hp := normalPDF_six_lt
    linarith
  have hk : transportRatio (-6) * normalPDF 6 = normalCDF 6 * (-Real.log (normalCDF 6)) := by
    unfold transportRatio exponentialTransport gaussianHazard
    rw [normalPDF_neg]
    norm_num only [neg_neg]
    field_simp
  have hloglo := Real.one_sub_inv_le_log_of_pos hc
  have hloghi := Real.log_le_sub_one_of_pos hc
  have hloglo' := mul_le_mul_of_nonneg_left hloglo hc.le
  rw [mul_sub, mul_one, mul_inv_cancel₀ hc.ne'] at hloglo'
  have hloghi' := mul_le_mul_of_nonneg_left hloghi hc.le
  have hupper : transportRatio (-6) ≤ millsApprox 9 6 := by
    apply (mul_le_mul_iff_right₀ hphi).mp
    norm_num [millsApprox, millsCoefficient]
    nlinarith [hloglo', href]
  have hpos : 0 < millsApprox 10 (6 : ℝ) := by norm_num [millsApprox, millsCoefficient]
  have hprod := mul_lt_mul_of_pos_right hsmall (mul_pos hphi hpos)
  have hscaled := mul_le_mul_of_nonneg_left hlo hc.le
  have hlower : (1 - 1 / 10000000) * millsApprox 10 6 < transportRatio (-6) := by
    apply (mul_lt_mul_iff_right₀ hphi).mp
    norm_num [millsApprox, millsCoefficient] at hprod ⊢
    nlinarith [hloghi', href]
  norm_num [millsApprox, millsCoefficient] at hupper hlower
  rw [abs_lt]
  constructor <;> linarith

end Submission.Lib.ScalarLog
