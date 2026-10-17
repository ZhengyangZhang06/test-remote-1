import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Approximation
import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Functions

namespace Submission.Obl.Entropy__two_eigenvalue_compact_certificate
open Submission.Lib.GaussianTransport

private theorem log_bound_first : (81/50 : ℝ) < Real.log (287/56) := by
  have h := Real.lt_log_one_add_of_pos (x := 9/32) (by norm_num)
  norm_num at h
  have he : Real.log (287/56 : ℝ) = 2*Real.log 2+Real.log (41/32) := by
    rw [show (287/56 : ℝ) = 2^2*(41/32) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [he]
  linarith [Real.log_two_gt_d9]

private theorem log_bound_second : (4 : ℝ) < Real.log (287/5) := by
  have h := Real.lt_log_one_add_of_pos (x := 127/160) (by norm_num)
  norm_num at h
  have he : Real.log (287/5 : ℝ) = 5*Real.log 2+Real.log (287/160) := by
    rw [show (287/5 : ℝ) = 2^5*(287/160) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [he]
  linarith [Real.log_two_gt_d9]

private theorem log_bound_third : (4 : ℝ) < Real.log 64 := by
  rw [show (64 : ℝ) = 2^6 by norm_num, Real.log_pow]
  norm_num
  linarith [Real.log_two_gt_d9]

private theorem log_bound_fourth : (13/2 : ℝ) < Real.log 768 := by
  have h := Real.lt_log_one_add_of_pos (x := 2) (by norm_num)
  norm_num at h
  rw [show (768 : ℝ) = 2^8*3 by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  norm_num
  linarith [Real.log_two_gt_d9]

private theorem log_gap (x y r s : ℝ) (hx : 0 < x) (hy : 0 < y) (hr : 0 < r)
    (hxy : r < x/y) (hs : s < Real.log r) : s < Real.log x-Real.log y := by
  rw [← Real.log_div hx.ne' hy.ne']
  exact hs.trans (Real.log_lt_log hr hxy)

theorem hazard_endpoint_bounds :
    (287/1000 : ℝ) < q (-1) ∧ q (-2) < 56/1000 ∧ q (-3) < 5/1000 ∧ 4 < q 4 := by
  have h1 := (abs_le.mp (approximation_3 1 (by norm_num)).1).1
  have h2 := (abs_le.mp (approximation_2 1 (by norm_num)).1).2
  have h3 := (abs_le.mp (approximation_2 (-1) (by norm_num)).1).2
  have e1 : model3.parameter 1 = -1 := by norm_num [Model.parameter, model3]
  have e2 : model2.parameter 1 = -2 := by norm_num [Model.parameter, model2]
  have e3 : model2.parameter (-1) = -3 := by norm_num [Model.parameter, model2]
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  norm_num [model3, peval] at h1
  norm_num [model2, peval] at h2 h3
  have h4 := gaussianGap_pos 4
  change 0 < q 4-4 at h4
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem endpoint_gaps :
    Real.log (q (-1))-Real.log (q (-2)) > 81/50 ∧
    Real.log (q (-1))-Real.log (q (-3)) > 4 ∧
    Real.log (q 4)-Real.log (q (-2)) > 4 ∧
    Real.log (q 4)-Real.log (q (-3)) > 13/2 := by
  obtain ⟨h1,h2,h3,h4⟩ := hazard_endpoint_bounds
  refine ⟨?_,?_,?_,?_⟩
  · apply log_gap _ _ (287/56) _ (gaussianHazard_pos _) (gaussianHazard_pos _)
      (by norm_num) _ log_bound_first
    apply (lt_div_iff₀ (gaussianHazard_pos _)).mpr
    nlinarith
  · apply log_gap _ _ (287/5) _ (gaussianHazard_pos _) (gaussianHazard_pos _)
      (by norm_num) _ log_bound_second
    apply (lt_div_iff₀ (gaussianHazard_pos _)).mpr
    nlinarith
  · apply log_gap _ _ 64 _ (gaussianHazard_pos _) (gaussianHazard_pos _)
      (by norm_num) _ log_bound_third
    apply (lt_div_iff₀ (gaussianHazard_pos _)).mpr
    nlinarith
  · apply log_gap _ _ 768 _ (gaussianHazard_pos _) (gaussianHazard_pos _)
      (by norm_num) _ log_bound_fourth
    apply (lt_div_iff₀ (gaussianHazard_pos _)).mpr
    nlinarith

end Submission.Obl.Entropy__two_eigenvalue_compact_certificate
