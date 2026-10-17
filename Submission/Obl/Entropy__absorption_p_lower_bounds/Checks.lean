import Submission.Obl.Entropy__absorption_p_lower_bounds.Expressions

namespace Submission.Obl.Entropy__absorption_p_lower_bounds

open Submission.Obl.Entropy__two_eigenvalue_compact_certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The two leftmost reserve certificates are already part of the accepted table. -/
theorem negative_check0 : (negativeExpr.enclose model0.initial).LowerBound (1/10^6) := by
  apply check_model0 negativeExpr
  exact List.getElem_mem (l := groups binO) (n := 5) (by decide)

theorem negative_check1 : (negativeExpr.enclose model1.initial).LowerBound (1/10^6) := by
  apply check_model1 negativeExpr
  exact List.getElem_mem (l := groups binO) (n := 5) (by decide)

theorem negative_check2 : (negativeExpr.enclose model2.initial).LowerBound (1/10^6) := by
  decide +kernel

theorem negative_check3 : (negativeExpr.enclose model3.initial).LowerBound (1/10^6) := by
  decide +kernel

theorem negative_check4 : (negativeExpr.enclose model4.initial).LowerBound (1/10^6) := by
  decide +kernel

theorem positive_check5 : ((positiveExpr (1/4)).enclose model5.initial).LowerBound (1/10^6) := by
  decide +kernel

theorem positive_check6 : ((positiveExpr (1/4)).enclose model6.initial).LowerBound (1/10^6) := by
  decide +kernel

theorem positive_check7 : ((positiveExpr (1/4)).enclose model7.initial).LowerBound (1/10^6) := by
  decide +kernel

theorem positive_check8 : ((positiveExpr (23/50)).enclose model8.initial).LowerBound (1/10^6) := by
  decide +kernel

theorem positive_check9 : ((positiveExpr (23/50)).enclose model9.initial).LowerBound (1/10^6) := by
  decide +kernel

theorem positive_check10 : ((positiveExpr (23/50)).enclose model10.initial).LowerBound (1/10^6) := by
  decide +kernel

end Submission.Obl.Entropy__absorption_p_lower_bounds
