import Submission.Lib.GaussianTransport.GaussianSlope

set_option backward.isDefEq.respectTransparency false

open Submission.Lib.GaussianTransport

namespace Submission.Obl.Entropy__two_eigenvalue_negative_certificate

lemma hasDerivAt_curvature (a : ℝ) : HasDerivAt transportCurvature
    (2 * transportSlope a - gaussianHazard a * gaussianGap a + a * transportCurvature a) a := by
  convert! ((hasDerivAt_transportRatio a).sub (hasDerivAt_gaussianHazard a)).add
    ((hasDerivAt_id a).mul (hasDerivAt_transportSlope a)) using 1
  simp only [id_eq, one_mul, gaussianGap]
  ring

lemma deriv_ratio : deriv transportRatio = transportSlope :=
  funext fun a => (hasDerivAt_transportRatio a).deriv

lemma deriv_slope : deriv transportSlope = transportCurvature :=
  funext fun a => (hasDerivAt_transportSlope a).deriv

lemma deriv_curvature (a : ℝ) : deriv transportCurvature a =
    2 * transportSlope a - gaussianHazard a * gaussianGap a + a * transportCurvature a :=
  (hasDerivAt_curvature a).deriv

lemma deriv_auxiliary (a : ℝ) :
    deriv (fun a => transportRatio a * (1 + transportSlope a)) a =
      transportSlope a * (1 + transportSlope a) + transportRatio a * transportCurvature a :=
  ((hasDerivAt_transportRatio a).mul ((hasDerivAt_transportSlope a).const_add 1)).deriv

end Submission.Obl.Entropy__two_eigenvalue_negative_certificate
