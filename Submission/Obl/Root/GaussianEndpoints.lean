import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Gaps

/-! Endpoint aliases for the accepted compact scalar certificate. -/

namespace Submission.Obl.Root.GaussianEndpoints

open Submission.Lib.GaussianTransport
open Submission.Obl.Entropy__two_eigenvalue_compact_certificate

theorem gaussianHazard_neg_three_lt : gaussianHazard (-3) < (1 : ℝ) / 200 := by
  convert hazard_endpoint_bounds.2.2.1 using 1 <;> norm_num

theorem gaussianHazard_neg_two_lt : gaussianHazard (-2) < (7 : ℝ) / 125 := by
  convert hazard_endpoint_bounds.2.1 using 1 <;> norm_num

theorem gaussianHazard_neg_one_gt : (287 : ℝ) / 1000 < gaussianHazard (-1) :=
  hazard_endpoint_bounds.1

/-- The same accepted central enclosure supplies the extra upper endpoint. -/
theorem gaussianHazard_neg_one_lt : gaussianHazard (-1) < (59 : ℝ) / 200 := by
  have h := (abs_le.mp (approximation_3 1 (by norm_num)).1).2
  have he : model3.parameter 1 = -1 := by norm_num [Model.parameter, model3]
  rw [he] at h
  norm_num [model3, peval] at h
  change q (-1) < 59 / 200
  linarith

theorem gaussianHazard_four_gt : (4 : ℝ) < gaussianHazard 4 :=
  hazard_endpoint_bounds.2.2.2

theorem log_hazard_neg_one_sub_neg_two_gt :
    (81 : ℝ) / 50 < Real.log (gaussianHazard (-1)) - Real.log (gaussianHazard (-2)) :=
  endpoint_gaps.1

theorem log_hazard_neg_one_sub_neg_three_gt :
    (4 : ℝ) < Real.log (gaussianHazard (-1)) - Real.log (gaussianHazard (-3)) :=
  endpoint_gaps.2.1

theorem log_hazard_four_sub_neg_two_gt :
    (4 : ℝ) < Real.log (gaussianHazard 4) - Real.log (gaussianHazard (-2)) :=
  endpoint_gaps.2.2.1

theorem log_hazard_four_sub_neg_three_gt :
    (13 : ℝ) / 2 < Real.log (gaussianHazard 4) - Real.log (gaussianHazard (-3)) :=
  endpoint_gaps.2.2.2

end Submission.Obl.Root.GaussianEndpoints
