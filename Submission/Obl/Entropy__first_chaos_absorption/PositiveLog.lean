import Mathlib

namespace Submission.Obl.Entropy__first_chaos_absorption

set_option backward.isDefEq.respectTransparency false

lemma positive_tail_log_bounds {r J : ℝ} (hr : 10 ≤ r)
    (hJlo : 1-(r⁻¹)^2 ≤ J) (hJhi : J ≤ 1) :
    let T := Real.log (r*Real.sqrt (2*Real.pi))-Real.log J
    3 ≤ T ∧ T/r ≤ 9/25 ∧ (r⁻¹)^2*(T-3/2) ≤ 1/40 := by
  have hr0 : 0 < r := by linarith
  have hs0 : 0 < Real.sqrt (2*Real.pi) := by positivity
  have hslo : (12/5 : ℝ) ≤ Real.sqrt (2*Real.pi) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  have hshi : Real.sqrt (2*Real.pi) ≤ 3 := by
    apply (Real.sqrt_le_left (by norm_num)).mpr
    nlinarith [Real.pi_lt_four]
  have he1lo : (27/10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he1hi : Real.exp 1 ≤ (11/4 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have he3 : Real.exp 3 ≤ (11/4 : ℝ)^3 := by
    calc
      _ = (Real.exp 1)^3 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ _ := by gcongr
  have hthetaLo : 3 ≤ Real.log (r*Real.sqrt (2*Real.pi)) := by
    apply (Real.le_log_iff_exp_le (mul_pos hr0 hs0)).mpr
    have hh := mul_le_mul hr hslo (by norm_num : (0 : ℝ) ≤ 12/5) hr0.le
    nlinarith only [he3, hh]
  have he7 : (27/10 : ℝ)^7 ≤ Real.exp 7 := by
    calc
      _ ≤ (Real.exp 1)^7 := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hehalf : 30 ≤ Real.exp (7/2) := by
    have heq : (Real.exp (7/2))^2 = Real.exp 7 := by rw [← Real.exp_nat_mul]; norm_num
    nlinarith only [he7, heq, Real.exp_pos (7/2)]
  have hanchor : Real.log (10*Real.sqrt (2*Real.pi)) ≤ 7/2 := by
    apply (Real.log_le_iff_le_exp (mul_pos (by norm_num) hs0)).mpr
    nlinarith only [hshi, hehalf]
  have hthetaHi : Real.log (r*Real.sqrt (2*Real.pi)) ≤ r/10+5/2 := by
    have hsplit : Real.log (r*Real.sqrt (2*Real.pi)) =
        Real.log (r/10)+Real.log (10*Real.sqrt (2*Real.pi)) := by
      rw [← Real.log_mul (by positivity : r/10 ≠ 0) (by positivity)]
      congr 1
      ring
    rw [hsplit]
    have hh := Real.log_le_sub_one_of_pos (div_pos hr0 (by norm_num : (0 : ℝ) < 10))
    linarith
  have hsmall : (r⁻¹)^2 ≤ 1/100 := by
    have hi : r⁻¹ ≤ (1/10 : ℝ) := (inv_le_comm₀ hr0 (by norm_num)).mpr (by simpa using hr)
    nlinarith [inv_pos.mpr hr0]
  have hJcap : 99/100 ≤ J := by linarith
  have hJpos : 0 < J := by linarith
  have hlogLo : -(1/50 : ℝ) ≤ Real.log J := by
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 99/100) hJcap
    norm_num only [one_div, inv_div, inv_inv] at hi
    have hh := Real.one_sub_inv_le_log_of_pos hJpos
    norm_num at hi
    linarith
  have hlogHi : Real.log J ≤ 0 := Real.log_nonpos hJpos.le hJhi
  let T := Real.log (r*Real.sqrt (2*Real.pi))-Real.log J
  have hTlo : 3 ≤ T := by dsimp [T]; linarith
  have hThi : T ≤ r/10+63/25 := by dsimp [T]; linarith
  refine ⟨hTlo, ?_, ?_⟩
  · change T/r ≤ 9/25
    apply (div_le_iff₀ hr0).mpr
    linarith
  · change (r⁻¹)^2*(T-3/2) ≤ 1/40
    have hh : T-3/2 ≤ (1/40)*r^2 := by nlinarith [sq_nonneg (r-10)]
    calc
      _ ≤ (r⁻¹)^2*((1/40)*r^2) := mul_le_mul_of_nonneg_left hh (sq_nonneg _)
      _ = _ := by field_simp

end Submission.Obl.Entropy__first_chaos_absorption
