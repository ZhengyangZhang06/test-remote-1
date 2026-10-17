import Submission.Lib.GaussianTransport.GaussianTails

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open Submission.Lib.GaussianTransport

namespace Submission.Obl.Entropy__two_eigenvalue_negative_certificate

lemma density_at_six : normalPDF 6 < 1 / 100000000 := by
  have hs : 2 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [Real.pi_gt_three]
  have he1 : (27 / 10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10) he1 18
  rw [Real.exp_one_pow] at he
  have he18 : 50000000 < Real.exp 18 := by norm_num at he ⊢; linarith
  unfold normalPDF ProbabilityTheory.gaussianPDFReal
  norm_num only [NNReal.coe_one, sub_zero, mul_one]
  rw [Real.exp_neg]
  have hp := Real.exp_pos (18 : ℝ)
  have hsp : 0 < Real.sqrt (2 * Real.pi) := by positivity
  rw [← mul_inv, inv_eq_one_div, div_lt_div_iff₀ (mul_pos hsp hp) (by norm_num)]
  nlinarith

/-- A uniform polynomial bound for the exponentially small tail errors. -/
lemma density_seventh_bound {r : ℝ} (hr : 6 ≤ r) :
    r ^ 7 * normalPDF r ≤ 1 / 300 := by
  have hd (x : ℝ) : HasDerivAt (fun x => x ^ 7 * normalPDF x)
      (x ^ 6 * (7 - x ^ 2) * normalPDF x) x := by
    convert! ((hasDerivAt_id x).pow 7).mul (hasDerivAt_normalPDF x) using 1
    simp only [id_eq, Pi.pow_apply]
    norm_num
    ring
  have hm : AntitoneOn (fun x => x ^ 7 * normalPDF x) (Ici 6) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _) 
      (by exact (continuous_id.pow 7 |>.mul contDiff_normalPDF.continuous).continuousOn)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(hd x).deriv]
    have hx6 : 6 < x := by simpa only [interior_Ici, mem_Ioi] using hx
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by nlinarith)) (normalPDF_pos x).le
  have h := hm (by simp) hr hr
  have h6 := density_at_six
  norm_num at h
  nlinarith

lemma density_bound {r : ℝ} (hr : 6 ≤ r) :
    normalPDF r ≤ 1 / (300 * r ^ 7) := by
  have hr0 : 0 < r := by linarith
  apply (le_div_iff₀ (by positivity : 0 < 300 * r ^ 7)).2
  nlinarith [density_seventh_bound hr]

end Submission.Obl.Entropy__two_eigenvalue_negative_certificate
