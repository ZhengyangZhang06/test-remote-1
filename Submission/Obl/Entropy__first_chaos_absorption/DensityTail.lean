import Submission.Lib.GaussianTransport.GaussianTails

open Set MeasureTheory ProbabilityTheory

namespace Submission.Obl.Entropy__first_chaos_absorption

set_option backward.isDefEq.respectTransparency false

open Submission.Lib.GaussianTransport

/-- A rational Gaussian error bound, uniform throughout the negative-tail
certificate range. -/
lemma normalPDF_mul_fifth_small {r : ℝ} (hr : 6 ≤ r) :
    normalPDF r*r^5 ≤ 1/1000 := by
  have hd (x : ℝ) : HasDerivAt (fun x => x^5*normalPDF x)
      (x^4*normalPDF x*(5-x^2)) x := by
    convert! ((hasDerivAt_id x).pow 5).mul (hasDerivAt_normalPDF x) using 1 <;> simp <;> ring
  have hm : AntitoneOn (fun x => x^5*normalPDF x) (Ici 6) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 6)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).hasDerivWithinAt)
      (fun x hx => by
        have hx' : 6 ≤ x := le_of_lt (by simpa using hx)
        exact mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg (pow_nonneg (by linarith : 0 ≤ x) _) (normalPDF_pos _).le)
          (by nlinarith))
  have hmono := hm (by simp : (6 : ℝ) ∈ Ici 6) hr hr
  have he1 : (27/10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he18 : (27/10 : ℝ)^18 ≤ Real.exp 18 := by
    calc
      _ ≤ (Real.exp 1)^18 := by gcongr
      _ = Real.exp 18 := by rw [← Real.exp_nat_mul]; norm_num
  have hsqrt : 1 ≤ Real.sqrt (2*Real.pi) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  have hp6 : normalPDF 6 ≤ (Real.exp 18)⁻¹ := by
    simp only [normalPDF, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
    rw [show -(6 : ℝ)^2 / 2 = -18 by norm_num, Real.exp_neg]
    have hs : (Real.sqrt (2*Real.pi))⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hsqrt
    exact mul_le_of_le_one_left (inv_pos.mpr (Real.exp_pos 18)).le hs
  have hnum : normalPDF 6 * (6 : ℝ)^5 ≤ 1/1000 := by
    calc
      _ ≤ (Real.exp 18)⁻¹*(6 : ℝ)^5 := by gcongr
      _ ≤ ((27/10 : ℝ)^18)⁻¹*(6 : ℝ)^5 := by gcongr
      _ ≤ 1/1000 := by norm_num
  nlinarith only [hmono, hnum]

end Submission.Obl.Entropy__first_chaos_absorption
