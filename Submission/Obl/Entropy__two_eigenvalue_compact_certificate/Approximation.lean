import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.ODEChecks
import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Anchors

namespace Submission.Obl.Entropy__two_eigenvalue_compact_certificate
open Submission.Lib.GaussianTransport

set_option maxRecDepth 100000

theorem q_error_10 (x : ℝ) (hx : |x| ≤ 1) :
    |gaussianHazard (model10.parameter x)-peval model10.hazard x| ≤ (37/50000000000 : ℝ) := by
  have ha : |gaussianHazard (model10.parameter 1)-peval model10.hazard 1| ≤ (3/5000000000 : ℝ) := by
    rw [show model10.parameter 1 = 10 by norm_num [Model.parameter, model10]]
    have h := abs_sub_le (gaussianHazard 10) (10098093234/10^9) (peval model10.hazard 1)
    linarith [hazard_anchor.le, q_anchor_polynomial]
  have h := ode_check_model10.hazard_step (by norm_num : 0 < (3/5000000000 : ℝ)) ha hx
  norm_num at h ⊢
  exact h

theorem q_error_9 (x : ℝ) (hx : |x| ≤ 1) :
    |gaussianHazard (model9.parameter x)-peval model9.hazard x| ≤ (27/25000000000 : ℝ) := by
  have ha : |gaussianHazard (model9.parameter 1)-peval model9.hazard 1| ≤ (47/50000000000 : ℝ) := by
    have he : model9.parameter 1 = model10.parameter (-1) := by norm_num [Model.parameter, model9, model10]
    have hq := q_error_10 (-1) (by norm_num)
    have hj := join_hazard9
    rw [abs_sub_comm] at hj
    have ht := abs_sub_le (gaussianHazard (model9.parameter 1)) (peval model10.hazard (-1)) (peval model9.hazard 1)
    rw [he] at ht ⊢
    linarith
  have h := ode_check_model9.hazard_step (by norm_num : 0 < (47/50000000000 : ℝ)) ha hx
  norm_num at h ⊢
  exact h

theorem q_error_8 (x : ℝ) (hx : |x| ≤ 1) :
    |gaussianHazard (model8.parameter x)-peval model8.hazard x| ≤ (71/50000000000 : ℝ) := by
  have ha : |gaussianHazard (model8.parameter 1)-peval model8.hazard 1| ≤ (1/781250000 : ℝ) := by
    have he : model8.parameter 1 = model9.parameter (-1) := by norm_num [Model.parameter, model8, model9]
    have hq := q_error_9 (-1) (by norm_num)
    have hj := join_hazard8
    rw [abs_sub_comm] at hj
    have ht := abs_sub_le (gaussianHazard (model8.parameter 1)) (peval model9.hazard (-1)) (peval model8.hazard 1)
    rw [he] at ht ⊢
    linarith
  have h := ode_check_model8.hazard_step (by norm_num : 0 < (1/781250000 : ℝ)) ha hx
  norm_num at h ⊢
  exact h

theorem q_error_7 (x : ℝ) (hx : |x| ≤ 1) :
    |gaussianHazard (model7.parameter x)-peval model7.hazard x| ≤ (11/6250000000 : ℝ) := by
  have ha : |gaussianHazard (model7.parameter 1)-peval model7.hazard 1| ≤ (81/50000000000 : ℝ) := by
    have he : model7.parameter 1 = model8.parameter (-1) := by norm_num [Model.parameter, model7, model8]
    have hq := q_error_8 (-1) (by norm_num)
    have hj := join_hazard7
    rw [abs_sub_comm] at hj
    have ht := abs_sub_le (gaussianHazard (model7.parameter 1)) (peval model8.hazard (-1)) (peval model7.hazard 1)
    rw [he] at ht ⊢
    linarith
  have h := ode_check_model7.hazard_step (by norm_num : 0 < (81/50000000000 : ℝ)) ha hx
  norm_num at h ⊢
  exact h

theorem q_error_6 (x : ℝ) (hx : |x| ≤ 1) :
    |gaussianHazard (model6.parameter x)-peval model6.hazard x| ≤ (21/10000000000 : ℝ) := by
  have ha : |gaussianHazard (model6.parameter 1)-peval model6.hazard 1| ≤ (49/25000000000 : ℝ) := by
    have he : model6.parameter 1 = model7.parameter (-1) := by norm_num [Model.parameter, model6, model7]
    have hq := q_error_7 (-1) (by norm_num)
    have hj := join_hazard6
    rw [abs_sub_comm] at hj
    have ht := abs_sub_le (gaussianHazard (model6.parameter 1)) (peval model7.hazard (-1)) (peval model6.hazard 1)
    rw [he] at ht ⊢
    linarith
  have h := ode_check_model6.hazard_step (by norm_num : 0 < (49/25000000000 : ℝ)) ha hx
  norm_num at h ⊢
  exact h

theorem q_error_5 (x : ℝ) (hx : |x| ≤ 1) :
    |gaussianHazard (model5.parameter x)-peval model5.hazard x| ≤ (61/25000000000 : ℝ) := by
  have ha : |gaussianHazard (model5.parameter 1)-peval model5.hazard 1| ≤ (23/10000000000 : ℝ) := by
    have he : model5.parameter 1 = model6.parameter (-1) := by norm_num [Model.parameter, model5, model6]
    have hq := q_error_6 (-1) (by norm_num)
    have hj := join_hazard5
    rw [abs_sub_comm] at hj
    have ht := abs_sub_le (gaussianHazard (model5.parameter 1)) (peval model6.hazard (-1)) (peval model5.hazard 1)
    rw [he] at ht ⊢
    linarith
  have h := ode_check_model5.hazard_step (by norm_num : 0 < (23/10000000000 : ℝ)) ha hx
  norm_num at h ⊢
  exact h

theorem q_error_4 (x : ℝ) (hx : |x| ≤ 1) :
    |gaussianHazard (model4.parameter x)-peval model4.hazard x| ≤ (139/50000000000 : ℝ) := by
  have ha : |gaussianHazard (model4.parameter 1)-peval model4.hazard 1| ≤ (33/12500000000 : ℝ) := by
    have he : model4.parameter 1 = model5.parameter (-1) := by norm_num [Model.parameter, model4, model5]
    have hq := q_error_5 (-1) (by norm_num)
    have hj := join_hazard4
    rw [abs_sub_comm] at hj
    have ht := abs_sub_le (gaussianHazard (model4.parameter 1)) (peval model5.hazard (-1)) (peval model4.hazard 1)
    rw [he] at ht ⊢
    linarith
  have h := ode_check_model4.hazard_step (by norm_num : 0 < (33/12500000000 : ℝ)) ha hx
  norm_num at h ⊢
  exact h

theorem q_error_3 (x : ℝ) (hx : |x| ≤ 1) :
    |gaussianHazard (model3.parameter x)-peval model3.hazard x| ≤ (39/12500000000 : ℝ) := by
  have ha : |gaussianHazard (model3.parameter 1)-peval model3.hazard 1| ≤ (149/50000000000 : ℝ) := by
    have he : model3.parameter 1 = model4.parameter (-1) := by norm_num [Model.parameter, model3, model4]
    have hq := q_error_4 (-1) (by norm_num)
    have hj := join_hazard3
    rw [abs_sub_comm] at hj
    have ht := abs_sub_le (gaussianHazard (model3.parameter 1)) (peval model4.hazard (-1)) (peval model3.hazard 1)
    rw [he] at ht ⊢
    linarith
  have h := ode_check_model3.hazard_step (by norm_num : 0 < (149/50000000000 : ℝ)) ha hx
  norm_num at h ⊢
  exact h

theorem q_error_2 (x : ℝ) (hx : |x| ≤ 1) :
    |gaussianHazard (model2.parameter x)-peval model2.hazard x| ≤ (173/50000000000 : ℝ) := by
  have ha : |gaussianHazard (model2.parameter 1)-peval model2.hazard 1| ≤ (83/25000000000 : ℝ) := by
    have he : model2.parameter 1 = model3.parameter (-1) := by norm_num [Model.parameter, model2, model3]
    have hq := q_error_3 (-1) (by norm_num)
    have hj := join_hazard2
    rw [abs_sub_comm] at hj
    have ht := abs_sub_le (gaussianHazard (model2.parameter 1)) (peval model3.hazard (-1)) (peval model2.hazard 1)
    rw [he] at ht ⊢
    linarith
  have h := ode_check_model2.hazard_step (by norm_num : 0 < (83/25000000000 : ℝ)) ha hx
  norm_num at h ⊢
  exact h

theorem q_error_1 (x : ℝ) (hx : |x| ≤ 1) :
    |gaussianHazard (model1.parameter x)-peval model1.hazard x| ≤ (383/50000000000 : ℝ) := by
  have ha : |gaussianHazard (model1.parameter 1)-peval model1.hazard 1| ≤ (183/50000000000 : ℝ) := by
    have he : model1.parameter 1 = model2.parameter (-1) := by norm_num [Model.parameter, model1, model2]
    have hq := q_error_2 (-1) (by norm_num)
    have hj := join_hazard1
    rw [abs_sub_comm] at hj
    have ht := abs_sub_le (gaussianHazard (model1.parameter 1)) (peval model2.hazard (-1)) (peval model1.hazard 1)
    rw [he] at ht ⊢
    linarith
  have h := ode_check_model1.hazard_step (by norm_num : 0 < (183/50000000000 : ℝ)) ha hx
  norm_num at h ⊢
  exact h

theorem q_error_0 (x : ℝ) (hx : |x| ≤ 1) :
    |gaussianHazard (model0.parameter x)-peval model0.hazard x| ≤ (1/125000000 : ℝ) := by
  have ha : |gaussianHazard (model0.parameter 1)-peval model0.hazard 1| ≤ (393/50000000000 : ℝ) := by
    have he : model0.parameter 1 = model1.parameter (-1) := by norm_num [Model.parameter, model0, model1]
    have hq := q_error_1 (-1) (by norm_num)
    have hj := join_hazard0
    rw [abs_sub_comm] at hj
    have ht := abs_sub_le (gaussianHazard (model0.parameter 1)) (peval model1.hazard (-1)) (peval model0.hazard 1)
    rw [he] at ht ⊢
    linarith
  have h := ode_check_model0.hazard_step (by norm_num : 0 < (393/50000000000 : ℝ)) ha hx
  norm_num at h ⊢
  exact h

theorem k_error_0 (x : ℝ) (hx : |x| ≤ 1) :
    |transportRatio (model0.parameter x)-peval model0.ratio x| ≤ (367/5000000000 : ℝ) := by
  have ha : |transportRatio (model0.parameter (-1))-peval model0.ratio (-1)| ≤ (43/1000000000 : ℝ) := by
    rw [show model0.parameter (-1) = -6 by norm_num [Model.parameter, model0]]
    have h := abs_sub_le (transportRatio (-6)) (16237766/10^8) (peval model0.ratio (-1))
    linarith [ratio_anchor.le, k_anchor_polynomial]
  have h := ode_check_model0.ratio_step (by norm_num : 0 < (43/1000000000 : ℝ)) ha
    (fun y hy => (q_error_0 y hy).trans (by norm_num)) hx
  rw [show (model0.radius : ℝ) = (3/4 : ℝ) by norm_num [model0]] at h
  norm_num at h ⊢
  exact h

theorem k_error_1 (x : ℝ) (hx : |x| ≤ 1) :
    |transportRatio (model1.parameter x)-peval model1.ratio x| ≤ (13/125000000 : ℝ) := by
  have ha : |transportRatio (model1.parameter (-1))-peval model1.ratio (-1)| ≤ (23/312500000 : ℝ) := by
    have he : model1.parameter (-1) = model0.parameter 1 := by norm_num [Model.parameter, model1, model0]
    have hk := k_error_0 1 (by norm_num)
    have hj := join_ratio0
    have ht := abs_sub_le (transportRatio (model1.parameter (-1))) (peval model0.ratio 1) (peval model1.ratio (-1))
    rw [he] at ht ⊢
    linarith
  have h := ode_check_model1.ratio_step (by norm_num : 0 < (23/312500000 : ℝ)) ha
    (fun y hy => (q_error_1 y hy).trans (by norm_num)) hx
  rw [show (model1.radius : ℝ) = (3/4 : ℝ) by norm_num [model1]] at h
  norm_num at h ⊢
  exact h

theorem k_error_2 (x : ℝ) (hx : |x| ≤ 1) :
    |transportRatio (model2.parameter x)-peval model2.ratio x| ≤ (623/5000000000 : ℝ) := by
  have ha : |transportRatio (model2.parameter (-1))-peval model2.ratio (-1)| ≤ (521/5000000000 : ℝ) := by
    have he : model2.parameter (-1) = model1.parameter 1 := by norm_num [Model.parameter, model2, model1]
    have hk := k_error_1 1 (by norm_num)
    have hj := join_ratio1
    have ht := abs_sub_le (transportRatio (model2.parameter (-1))) (peval model1.ratio 1) (peval model2.ratio (-1))
    rw [he] at ht ⊢
    linarith
  have h := ode_check_model2.ratio_step (by norm_num : 0 < (521/5000000000 : ℝ)) ha
    (fun y hy => (q_error_2 y hy).trans (by norm_num)) hx
  rw [show (model2.radius : ℝ) = (1/2 : ℝ) by norm_num [model2]] at h
  norm_num at h ⊢
  exact h

theorem k_error_3 (x : ℝ) (hx : |x| ≤ 1) :
    |transportRatio (model3.parameter x)-peval model3.ratio x| ≤ (363/2500000000 : ℝ) := by
  have ha : |transportRatio (model3.parameter (-1))-peval model3.ratio (-1)| ≤ (39/312500000 : ℝ) := by
    have he : model3.parameter (-1) = model2.parameter 1 := by norm_num [Model.parameter, model3, model2]
    have hk := k_error_2 1 (by norm_num)
    have hj := join_ratio2
    have ht := abs_sub_le (transportRatio (model3.parameter (-1))) (peval model2.ratio 1) (peval model3.ratio (-1))
    rw [he] at ht ⊢
    linarith
  have h := ode_check_model3.ratio_step (by norm_num : 0 < (39/312500000 : ℝ)) ha
    (fun y hy => (q_error_3 y hy).trans (by norm_num)) hx
  rw [show (model3.radius : ℝ) = (1/2 : ℝ) by norm_num [model3]] at h
  norm_num at h ⊢
  exact h

theorem k_error_4 (x : ℝ) (hx : |x| ≤ 1) :
    |transportRatio (model4.parameter x)-peval model4.ratio x| ≤ (829/5000000000 : ℝ) := by
  have ha : |transportRatio (model4.parameter (-1))-peval model4.ratio (-1)| ≤ (727/5000000000 : ℝ) := by
    have he : model4.parameter (-1) = model3.parameter 1 := by norm_num [Model.parameter, model4, model3]
    have hk := k_error_3 1 (by norm_num)
    have hj := join_ratio3
    have ht := abs_sub_le (transportRatio (model4.parameter (-1))) (peval model3.ratio 1) (peval model4.ratio (-1))
    rw [he] at ht ⊢
    linarith
  have h := ode_check_model4.ratio_step (by norm_num : 0 < (727/5000000000 : ℝ)) ha
    (fun y hy => (q_error_4 y hy).trans (by norm_num)) hx
  rw [show (model4.radius : ℝ) = (1/2 : ℝ) by norm_num [model4]] at h
  norm_num at h ⊢
  exact h

theorem k_error_5 (x : ℝ) (hx : |x| ≤ 1) :
    |transportRatio (model5.parameter x)-peval model5.ratio x| ≤ (441/2500000000 : ℝ) := by
  have ha : |transportRatio (model5.parameter (-1))-peval model5.ratio (-1)| ≤ (83/500000000 : ℝ) := by
    have he : model5.parameter (-1) = model4.parameter 1 := by norm_num [Model.parameter, model5, model4]
    have hk := k_error_4 1 (by norm_num)
    have hj := join_ratio4
    have ht := abs_sub_le (transportRatio (model5.parameter (-1))) (peval model4.ratio 1) (peval model5.ratio (-1))
    rw [he] at ht ⊢
    linarith
  have h := ode_check_model5.ratio_step (by norm_num : 0 < (83/500000000 : ℝ)) ha
    (fun y hy => (q_error_5 y hy).trans (by norm_num)) hx
  rw [show (model5.radius : ℝ) = (1/4 : ℝ) by norm_num [model5]] at h
  norm_num at h ⊢
  exact h

theorem k_error_6 (x : ℝ) (hx : |x| ≤ 1) :
    |transportRatio (model6.parameter x)-peval model6.ratio x| ≤ (261/1000000000 : ℝ) := by
  have ha : |transportRatio (model6.parameter (-1))-peval model6.ratio (-1)| ≤ (883/5000000000 : ℝ) := by
    have he : model6.parameter (-1) = model5.parameter 1 := by norm_num [Model.parameter, model6, model5]
    have hk := k_error_5 1 (by norm_num)
    have hj := join_ratio5
    have ht := abs_sub_le (transportRatio (model6.parameter (-1))) (peval model5.ratio 1) (peval model6.ratio (-1))
    rw [he] at ht ⊢
    linarith
  have h := ode_check_model6.ratio_step (by norm_num : 0 < (883/5000000000 : ℝ)) ha
    (fun y hy => (q_error_6 y hy).trans (by norm_num)) hx
  rw [show (model6.radius : ℝ) = (3/4 : ℝ) by norm_num [model6]] at h
  norm_num at h ⊢
  exact h

theorem k_error_7 (x : ℝ) (hx : |x| ≤ 1) :
    |transportRatio (model7.parameter x)-peval model7.ratio x| ≤ (467/1250000000 : ℝ) := by
  have ha : |transportRatio (model7.parameter (-1))-peval model7.ratio (-1)| ≤ (653/2500000000 : ℝ) := by
    have he : model7.parameter (-1) = model6.parameter 1 := by norm_num [Model.parameter, model7, model6]
    have hk := k_error_6 1 (by norm_num)
    have hj := join_ratio6
    have ht := abs_sub_le (transportRatio (model7.parameter (-1))) (peval model6.ratio 1) (peval model7.ratio (-1))
    rw [he] at ht ⊢
    linarith
  have h := ode_check_model7.ratio_step (by norm_num : 0 < (653/2500000000 : ℝ)) ha
    (fun y hy => (q_error_7 y hy).trans (by norm_num)) hx
  rw [show (model7.radius : ℝ) = (1/1 : ℝ) by norm_num [model7]] at h
  norm_num at h ⊢
  exact h

theorem k_error_8 (x : ℝ) (hx : |x| ≤ 1) :
    |transportRatio (model8.parameter x)-peval model8.ratio x| ≤ (2431/5000000000 : ℝ) := by
  have ha : |transportRatio (model8.parameter (-1))-peval model8.ratio (-1)| ≤ (1869/5000000000 : ℝ) := by
    have he : model8.parameter (-1) = model7.parameter 1 := by norm_num [Model.parameter, model8, model7]
    have hk := k_error_7 1 (by norm_num)
    have hj := join_ratio7
    have ht := abs_sub_le (transportRatio (model8.parameter (-1))) (peval model7.ratio 1) (peval model8.ratio (-1))
    rw [he] at ht ⊢
    linarith
  have h := ode_check_model8.ratio_step (by norm_num : 0 < (1869/5000000000 : ℝ)) ha
    (fun y hy => (q_error_8 y hy).trans (by norm_num)) hx
  rw [show (model8.radius : ℝ) = (1/1 : ℝ) by norm_num [model8]] at h
  norm_num at h ⊢
  exact h

theorem k_error_9 (x : ℝ) (hx : |x| ≤ 1) :
    |transportRatio (model9.parameter x)-peval model9.ratio x| ≤ (1497/2500000000 : ℝ) := by
  have ha : |transportRatio (model9.parameter (-1))-peval model9.ratio (-1)| ≤ (19/39062500 : ℝ) := by
    have he : model9.parameter (-1) = model8.parameter 1 := by norm_num [Model.parameter, model9, model8]
    have hk := k_error_8 1 (by norm_num)
    have hj := join_ratio8
    have ht := abs_sub_le (transportRatio (model9.parameter (-1))) (peval model8.ratio 1) (peval model9.ratio (-1))
    rw [he] at ht ⊢
    linarith
  have h := ode_check_model9.ratio_step (by norm_num : 0 < (19/39062500 : ℝ)) ha
    (fun y hy => (q_error_9 y hy).trans (by norm_num)) hx
  rw [show (model9.radius : ℝ) = (1/1 : ℝ) by norm_num [model9]] at h
  norm_num at h ⊢
  exact h

theorem k_error_10 (x : ℝ) (hx : |x| ≤ 1) :
    |transportRatio (model10.parameter x)-peval model10.ratio x| ≤ (3557/5000000000 : ℝ) := by
  have ha : |transportRatio (model10.parameter (-1))-peval model10.ratio (-1)| ≤ (599/1000000000 : ℝ) := by
    have he : model10.parameter (-1) = model9.parameter 1 := by norm_num [Model.parameter, model10, model9]
    have hk := k_error_9 1 (by norm_num)
    have hj := join_ratio9
    have ht := abs_sub_le (transportRatio (model10.parameter (-1))) (peval model9.ratio 1) (peval model10.ratio (-1))
    rw [he] at ht ⊢
    linarith
  have h := ode_check_model10.ratio_step (by norm_num : 0 < (599/1000000000 : ℝ)) ha
    (fun y hy => (q_error_10 y hy).trans (by norm_num)) hx
  rw [show (model10.radius : ℝ) = (1/1 : ℝ) by norm_num [model10]] at h
  norm_num at h ⊢
  exact h

theorem approximation_0 (x : ℝ) (hx : |x| ≤ 1) :
    |gaussianHazard (model0.parameter x)-peval model0.hazard x| ≤ (1/10^8 : ℝ) ∧
    |transportRatio (model0.parameter x)-peval model0.ratio x| ≤ (8/10^7 : ℝ) :=
  ⟨(q_error_0 x hx).trans (by norm_num), (k_error_0 x hx).trans (by norm_num)⟩

theorem approximation_1 (x : ℝ) (hx : |x| ≤ 1) :
    |gaussianHazard (model1.parameter x)-peval model1.hazard x| ≤ (1/10^8 : ℝ) ∧
    |transportRatio (model1.parameter x)-peval model1.ratio x| ≤ (8/10^7 : ℝ) :=
  ⟨(q_error_1 x hx).trans (by norm_num), (k_error_1 x hx).trans (by norm_num)⟩

theorem approximation_2 (x : ℝ) (hx : |x| ≤ 1) :
    |gaussianHazard (model2.parameter x)-peval model2.hazard x| ≤ (1/10^8 : ℝ) ∧
    |transportRatio (model2.parameter x)-peval model2.ratio x| ≤ (8/10^7 : ℝ) :=
  ⟨(q_error_2 x hx).trans (by norm_num), (k_error_2 x hx).trans (by norm_num)⟩

theorem approximation_3 (x : ℝ) (hx : |x| ≤ 1) :
    |gaussianHazard (model3.parameter x)-peval model3.hazard x| ≤ (1/10^8 : ℝ) ∧
    |transportRatio (model3.parameter x)-peval model3.ratio x| ≤ (8/10^7 : ℝ) :=
  ⟨(q_error_3 x hx).trans (by norm_num), (k_error_3 x hx).trans (by norm_num)⟩

theorem approximation_4 (x : ℝ) (hx : |x| ≤ 1) :
    |gaussianHazard (model4.parameter x)-peval model4.hazard x| ≤ (1/10^8 : ℝ) ∧
    |transportRatio (model4.parameter x)-peval model4.ratio x| ≤ (8/10^7 : ℝ) :=
  ⟨(q_error_4 x hx).trans (by norm_num), (k_error_4 x hx).trans (by norm_num)⟩

theorem approximation_5 (x : ℝ) (hx : |x| ≤ 1) :
    |gaussianHazard (model5.parameter x)-peval model5.hazard x| ≤ (1/10^8 : ℝ) ∧
    |transportRatio (model5.parameter x)-peval model5.ratio x| ≤ (8/10^7 : ℝ) :=
  ⟨(q_error_5 x hx).trans (by norm_num), (k_error_5 x hx).trans (by norm_num)⟩

theorem approximation_6 (x : ℝ) (hx : |x| ≤ 1) :
    |gaussianHazard (model6.parameter x)-peval model6.hazard x| ≤ (1/10^8 : ℝ) ∧
    |transportRatio (model6.parameter x)-peval model6.ratio x| ≤ (8/10^7 : ℝ) :=
  ⟨(q_error_6 x hx).trans (by norm_num), (k_error_6 x hx).trans (by norm_num)⟩

theorem approximation_7 (x : ℝ) (hx : |x| ≤ 1) :
    |gaussianHazard (model7.parameter x)-peval model7.hazard x| ≤ (1/10^8 : ℝ) ∧
    |transportRatio (model7.parameter x)-peval model7.ratio x| ≤ (8/10^7 : ℝ) :=
  ⟨(q_error_7 x hx).trans (by norm_num), (k_error_7 x hx).trans (by norm_num)⟩

theorem approximation_8 (x : ℝ) (hx : |x| ≤ 1) :
    |gaussianHazard (model8.parameter x)-peval model8.hazard x| ≤ (1/10^8 : ℝ) ∧
    |transportRatio (model8.parameter x)-peval model8.ratio x| ≤ (8/10^7 : ℝ) :=
  ⟨(q_error_8 x hx).trans (by norm_num), (k_error_8 x hx).trans (by norm_num)⟩

theorem approximation_9 (x : ℝ) (hx : |x| ≤ 1) :
    |gaussianHazard (model9.parameter x)-peval model9.hazard x| ≤ (1/10^8 : ℝ) ∧
    |transportRatio (model9.parameter x)-peval model9.ratio x| ≤ (8/10^7 : ℝ) :=
  ⟨(q_error_9 x hx).trans (by norm_num), (k_error_9 x hx).trans (by norm_num)⟩

theorem approximation_10 (x : ℝ) (hx : |x| ≤ 1) :
    |gaussianHazard (model10.parameter x)-peval model10.hazard x| ≤ (1/10^8 : ℝ) ∧
    |transportRatio (model10.parameter x)-peval model10.ratio x| ≤ (8/10^7 : ℝ) :=
  ⟨(q_error_10 x hx).trans (by norm_num), (k_error_10 x hx).trans (by norm_num)⟩

end Submission.Obl.Entropy__two_eigenvalue_compact_certificate
