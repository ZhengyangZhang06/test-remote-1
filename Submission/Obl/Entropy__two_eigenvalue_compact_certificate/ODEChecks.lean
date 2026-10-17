import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Propagation
import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Data

namespace Submission.Obl.Entropy__two_eigenvalue_compact_certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ode_check_model0 : model0.ODECheck (7/10^11) 2 := by decide +kernel

theorem ode_check_model1 : model1.ODECheck (2/10^9) 2 := by decide +kernel

theorem ode_check_model2 : model2.ODECheck (7/10^11) 2 := by decide +kernel

theorem ode_check_model3 : model3.ODECheck (7/10^11) 2 := by decide +kernel

theorem ode_check_model4 : model4.ODECheck (7/10^11) 2 := by decide +kernel

theorem ode_check_model5 : model5.ODECheck (7/10^11) 2 := by decide +kernel

theorem ode_check_model6 : model6.ODECheck (7/10^11) (28/5) := by decide +kernel

theorem ode_check_model7 : model7.ODECheck (7/10^11) (28/5) := by decide +kernel

theorem ode_check_model8 : model8.ODECheck (7/10^11) (28/5) := by decide +kernel

theorem ode_check_model9 : model9.ODECheck (7/10^11) (28/5) := by decide +kernel

theorem ode_check_model10 : model10.ODECheck (7/10^11) (28/5) := by decide +kernel

theorem join_hazard0 : |peval model0.hazard 1-peval model1.hazard (-1)| ≤ (2/10^10 : ℝ) := by
  norm_num [peval, model0, model1]

theorem join_ratio0 : |peval model0.ratio 1-peval model1.ratio (-1)| ≤ (2/10^10 : ℝ) := by
  norm_num [peval, model0, model1]

theorem join_hazard1 : |peval model1.hazard 1-peval model2.hazard (-1)| ≤ (2/10^10 : ℝ) := by
  norm_num [peval, model1, model2]

theorem join_ratio1 : |peval model1.ratio 1-peval model2.ratio (-1)| ≤ (2/10^10 : ℝ) := by
  norm_num [peval, model1, model2]

theorem join_hazard2 : |peval model2.hazard 1-peval model3.hazard (-1)| ≤ (2/10^10 : ℝ) := by
  norm_num [peval, model2, model3]

theorem join_ratio2 : |peval model2.ratio 1-peval model3.ratio (-1)| ≤ (2/10^10 : ℝ) := by
  norm_num [peval, model2, model3]

theorem join_hazard3 : |peval model3.hazard 1-peval model4.hazard (-1)| ≤ (2/10^10 : ℝ) := by
  norm_num [peval, model3, model4]

theorem join_ratio3 : |peval model3.ratio 1-peval model4.ratio (-1)| ≤ (2/10^10 : ℝ) := by
  norm_num [peval, model3, model4]

theorem join_hazard4 : |peval model4.hazard 1-peval model5.hazard (-1)| ≤ (2/10^10 : ℝ) := by
  norm_num [peval, model4, model5]

theorem join_ratio4 : |peval model4.ratio 1-peval model5.ratio (-1)| ≤ (2/10^10 : ℝ) := by
  norm_num [peval, model4, model5]

theorem join_hazard5 : |peval model5.hazard 1-peval model6.hazard (-1)| ≤ (2/10^10 : ℝ) := by
  norm_num [peval, model5, model6]

theorem join_ratio5 : |peval model5.ratio 1-peval model6.ratio (-1)| ≤ (2/10^10 : ℝ) := by
  norm_num [peval, model5, model6]

theorem join_hazard6 : |peval model6.hazard 1-peval model7.hazard (-1)| ≤ (2/10^10 : ℝ) := by
  norm_num [peval, model6, model7]

theorem join_ratio6 : |peval model6.ratio 1-peval model7.ratio (-1)| ≤ (2/10^10 : ℝ) := by
  norm_num [peval, model6, model7]

theorem join_hazard7 : |peval model7.hazard 1-peval model8.hazard (-1)| ≤ (2/10^10 : ℝ) := by
  norm_num [peval, model7, model8]

theorem join_ratio7 : |peval model7.ratio 1-peval model8.ratio (-1)| ≤ (2/10^10 : ℝ) := by
  norm_num [peval, model7, model8]

theorem join_hazard8 : |peval model8.hazard 1-peval model9.hazard (-1)| ≤ (2/10^10 : ℝ) := by
  norm_num [peval, model8, model9]

theorem join_ratio8 : |peval model8.ratio 1-peval model9.ratio (-1)| ≤ (2/10^10 : ℝ) := by
  norm_num [peval, model8, model9]

theorem join_hazard9 : |peval model9.hazard 1-peval model10.hazard (-1)| ≤ (2/10^10 : ℝ) := by
  norm_num [peval, model9, model10]

theorem join_ratio9 : |peval model9.ratio 1-peval model10.ratio (-1)| ≤ (2/10^10 : ℝ) := by
  norm_num [peval, model9, model10]

theorem q_anchor_polynomial : |10098093234/10^9-peval model10.hazard 1| ≤ (2/10^10 : ℝ) := by
  norm_num [peval, model10]

theorem k_anchor_polynomial : |16237766/10^8-peval model0.ratio (-1)| ≤ (3/10^9 : ℝ) := by
  norm_num [peval, model0]

end Submission.Obl.Entropy__two_eigenvalue_compact_certificate
