import Submission.Obl.Entropy__first_chaos_absorption.Mills
import Submission.Obl.Entropy__first_chaos_absorption.PositiveMills

open MeasureTheory ProbabilityTheory

namespace Submission.Obl.Entropy__first_chaos_absorption

set_option backward.isDefEq.respectTransparency false

open Submission.Lib.GaussianTransport

lemma positive_tail_forms {r : ℝ} (hr : 0 < r) :
    let u := (r⁻¹)^2
    let J := r*(normalCDF (-r)/normalPDF r)
    let T := Real.log (r*Real.sqrt (2*Real.pi))-Real.log J
    gaussianHazard r = r/J ∧
    transportRatio r = r*J*(1/2+u*T) ∧
    transportSlope r = 1-(1/(2*u)+T)*(1-J) ∧
    transportCurvature r = r*millsCurvature u T J := by
  let u := (r⁻¹)^2
  let J := r*(normalCDF (-r)/normalPDF r)
  let T := Real.log (r*Real.sqrt (2*Real.pi))-Real.log J
  have hJ : 0 < J := mul_pos hr (div_pos (normalCDF_pos _) (normalPDF_pos _))
  have hs : 0 < Real.sqrt (2*Real.pi) := by positivity
  have hPDF : Real.log (normalPDF r) = -Real.log (Real.sqrt (2*Real.pi))-r^2/2 := by
    simp only [normalPDF, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
    rw [Real.log_mul (inv_ne_zero hs.ne') (Real.exp_ne_zero _), Real.log_inv, Real.log_exp]
    ring
  have hCDF : normalCDF (-r) = J*normalPDF r/r := by
    dsimp [J]
    field_simp [(normalPDF_pos r).ne']
  have hlog : Real.log (normalCDF (-r)) = Real.log J+Real.log (normalPDF r)-Real.log r := by
    rw [hCDF, Real.log_div (mul_ne_zero hJ.ne' (normalPDF_pos _).ne') hr.ne',
      Real.log_mul hJ.ne' (normalPDF_pos _).ne']
  have ht : exponentialTransport r = r^2/2+T := by
    unfold exponentialTransport
    rw [hlog, hPDF]
    dsimp [T]
    rw [Real.log_mul hr.ne' hs.ne']
    ring
  have hq : gaussianHazard r = r/J := by
    dsimp [gaussianHazard, J]
    field_simp
  have hk : transportRatio r = r*J*(1/2+u*T) := by
    rw [transportRatio, ht, hq]
    dsimp [u]
    field_simp [hr.ne', hJ.ne']
  have hb : transportSlope r = 1-(1/(2*u)+T)*(1-J) := by
    rw [transportSlope, gaussianGap, hk, hq]
    dsimp [u]
    field_simp [hr.ne', hJ.ne']
  have hl : transportCurvature r = r*millsCurvature u T J := by
    rw [transportCurvature, hk, hq, hb]
    unfold millsCurvature
    dsimp [u]
    field_simp [hr.ne', hJ.ne'] <;> ring
  exact ⟨hq, hk, hb, hl⟩

end Submission.Obl.Entropy__first_chaos_absorption
