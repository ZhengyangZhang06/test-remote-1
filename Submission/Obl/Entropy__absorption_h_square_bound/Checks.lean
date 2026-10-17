import Submission.Obl.Entropy__absorption_h_square_bound.Certificate
import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Data

namespace Submission.Obl.Entropy__absorption_h_square_bound

open Submission.Obl.Entropy__two_eigenvalue_compact_certificate
open scoped Submission.Obl.Entropy__two_eigenvalue_compact_certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem square_check0 : (squareGap.enclose model0.initial).LowerBound 0 := by decide +kernel
theorem square_check1 : (squareGap.enclose model1.initial).LowerBound 0 := by decide +kernel
theorem square_check2 : (squareGap.enclose model2.initial).LowerBound 0 := by decide +kernel
theorem square_check3 : (squareGap.enclose model3.initial).LowerBound 0 := by decide +kernel
theorem square_check4 : (squareGap.enclose model4.initial).LowerBound 0 := by decide +kernel
theorem square_check5 : (squareGap.enclose model5.initial).LowerBound 0 := by decide +kernel
theorem square_check6 : (squareGap.enclose model6.initial).LowerBound 0 := by decide +kernel
theorem square_check7 : (squareGap.enclose model7.initial).LowerBound 0 := by decide +kernel
theorem square_check8 : (squareGap.enclose model8.initial).LowerBound 0 := by decide +kernel
theorem square_check9 : (squareGap.enclose model9.initial).LowerBound 0 := by decide +kernel
theorem square_check10 : (squareGap.enclose model10.initial).LowerBound 0 := by decide +kernel

end Submission.Obl.Entropy__absorption_h_square_bound
