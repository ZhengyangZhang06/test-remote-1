import Submission.Lib.GaussianTransport.GaussianSlope

open scoped ContDiff

namespace Submission.Obl.Entropy__first_chaos_absorption

open Submission.Lib.GaussianTransport

/-- The algebraic form of the scalar reserve p in Appendix A. -/
noncomputable def pValue (a : ℝ) : ℝ :=
  transportSlope a + transportRatio a * transportCurvature a - (40/3)*(transportCurvature a)^2

/-- The algebraic form of h₀ in Appendix A. -/
noncomputable def hValue (a : ℝ) : ℝ :=
  transportRatio a * (transportSlope a - 1/2) -
    (80/3)*(transportSlope a - 7/25)*transportCurvature a

noncomputable def yCostValue (a : ℝ) : ℝ :=
  (40/37)*((transportSlope a - 7/25)^2 + (5/96)*(hValue a)^2 / pValue a)

lemma deriv_transportRatio_eq : deriv transportRatio = transportSlope := by
  funext a
  exact (hasDerivAt_transportRatio a).deriv

lemma deriv_transportSlope_eq : deriv transportSlope = transportCurvature := by
  funext a
  exact (hasDerivAt_transportSlope a).deriv

lemma pValue_eq_deriv (a : ℝ) :
    pValue a = deriv (fun z => transportRatio z * (1 + transportSlope z)) a -
      (transportSlope a)^2 - (40/3)*(transportCurvature a)^2 := by
  have hd : deriv (fun z => transportRatio z * (1 + transportSlope z)) a =
      transportSlope a * (1 + transportSlope a) + transportRatio a * transportCurvature a := by
    exact ((hasDerivAt_transportRatio a).mul ((hasDerivAt_transportSlope a).const_add 1)).deriv
  rw [hd]
  unfold pValue
  ring

lemma hValue_eq (a : ℝ) :
    hValue a = transportRatio a * (1 + transportSlope a) - (3/2)*transportRatio a -
      (80/3)*(transportSlope a - 7/25)*transportCurvature a := by
  unfold hValue
  ring

lemma continuous_pValue : Continuous pValue := by
  have hk : Continuous transportRatio :=
    (show Differentiable ℝ transportRatio from fun a =>
      (hasDerivAt_transportRatio a).differentiableAt).continuous
  have hb : Continuous transportSlope :=
    (show Differentiable ℝ transportSlope from fun a =>
      (hasDerivAt_transportSlope a).differentiableAt).continuous
  have hl : Continuous transportCurvature := by
    unfold transportCurvature
    exact (hk.sub contDiff_gaussianHazard.continuous).add (continuous_id.mul hb)
  exact (hb.add (hk.mul hl)).sub (continuous_const.mul (hl.pow 2))

/-- The reserve used by the frozen statement equals the algebraic certificate
function, after the derivative identifications from GaussianTransport. -/
lemma frozen_p_eq :
    (fun a => deriv (fun z => transportRatio z * (1 + deriv transportRatio z)) a -
      (deriv transportRatio a)^2 - (40/3)*(deriv (deriv transportRatio) a)^2) = pValue := by
  rw [deriv_transportRatio_eq, deriv_transportSlope_eq]
  exact funext fun a => (pValue_eq_deriv a).symm

lemma frozen_h_eq :
    (fun a => transportRatio a * (1 + deriv transportRatio a) - (3/2)*transportRatio a -
      (80/3)*(deriv transportRatio a - 7/25)*deriv (deriv transportRatio) a) = hValue := by
  rw [deriv_transportRatio_eq, deriv_transportSlope_eq]
  exact funext fun a => (hValue_eq a).symm

end Submission.Obl.Entropy__first_chaos_absorption
