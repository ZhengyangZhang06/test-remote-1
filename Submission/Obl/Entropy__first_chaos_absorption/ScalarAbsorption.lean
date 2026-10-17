import Submission.Obl.Entropy__first_chaos_absorption.Assembly
import Submission.Obl.Entropy__first_chaos_absorption.ScalarMinorant
import Submission.Obl.Entropy__absorption_logarithmic_cutoff

namespace Submission.Obl.Entropy__first_chaos_absorption

open Submission.Lib.EntropyTools

lemma scalar_absorption_bound {z r e : ℝ} (hz : 0 ≤ z) (hr : 0 ≤ r)
    (he : rigidityCutoff z - minorantLoss (rigidityCutoff z)*(z+r) ≤ e) :
    dualSVal z - 1 - Real.log (dualSVal z) - dualWVal z * e ≤
      (27/1000)*r - rigidityWeight z/1000 := by
  have hd := minorantLoss_mul_parameter hz
  have helow : (689/1000)*rigidityCutoff z - minorantLoss (rigidityCutoff z)*r ≤ e := by
    nlinarith only [he, hd]
  have hlog := Submission.Entropy.absorption_logarithmic_cutoff z hz
  change 40/(37+3*z) - 1 - Real.log (40/(37+3*z)) ≤ (86/125)*rigidityWeight z at hlog
  rw [← dualSVal_eq] at hlog
  change dualSVal z - 1 - Real.log (dualSVal z) ≤
    (86/125)*(absorptionH z*absorptionRho z*rigidityCutoff z) at hlog
  have hwe := mul_le_mul_of_nonneg_left helow
    (mul_nonneg (absorptionH_nonneg hz) (absorptionRho_nonneg hz))
  have hwr := mul_le_mul_of_nonneg_right (weighted_minorantLoss_le hz) hr
  rw [dualWVal_eq hz]
  change dualSVal z - 1 - Real.log (dualSVal z) - (absorptionH z*absorptionRho z)*e ≤
    (27/1000)*r - (absorptionH z*absorptionRho z*rigidityCutoff z)/1000
  nlinarith only [hlog, hwe, hwr]

end Submission.Obl.Entropy__first_chaos_absorption
