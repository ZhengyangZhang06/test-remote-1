import Submission.Obl.Entropy__two_eigenvalue_secant_deduction.Costs

open Set

namespace Submission.Obl.Entropy__two_eigenvalue_secant_deduction
open Submission.Lib.GaussianTransport

lemma F_R {j a : ℝ} (hj : Certificate j) (ha : Certificate a) (hbin : -2 ≤ j ∧ j < -1) :
    Fcost j a ≤ 59/200 := by
  by_cases h : a < -1
  · exact (F_R_neg hj ha hbin h).trans (by norm_num)
  · exact F_R_pos hj ha hbin (le_of_not_gt h)
lemma F_UV {j a : ℝ} (hj : Certificate j) (ha : Certificate a) (hbin : -1 ≤ j ∧ j < 4) :
    Fcost j a ≤ 23/100 := by
  by_cases h : j < 1/2
  · by_cases ha' : a < -1
    · exact F_U_neg hj ha ⟨hbin.1,h⟩ ha'
    · exact F_U_pos hj ha ⟨hbin.1,h⟩ (le_of_not_gt ha')
  · by_cases ha' : a < -1
    · exact F_V_neg hj ha ⟨le_of_not_gt h,hbin.2⟩ ha'
    · exact F_V_pos hj ha ⟨le_of_not_gt h,hbin.2⟩ (le_of_not_gt ha')
lemma F_T {j a : ℝ} (hj : Certificate j) (ha : Certificate a) (hbin : 4 ≤ j) :
    Fcost j a ≤ 39/100 := by
  by_cases h : a < -1
  · exact F_T_neg hj ha hbin h
  · exact F_T_pos hj ha hbin (le_of_not_gt h)
lemma F_P {j a : ℝ} (hj : Certificate j) (ha : Certificate a) (hbin : -3 ≤ j ∧ j < -2) :
    Fcost j a ≤ (61/100)^2 := by
  by_cases h : a < -1
  · exact (F_P_neg hj ha hbin h).trans (by norm_num)
  · exact F_P_pos hj ha hbin (le_of_not_gt h)
lemma F_ge_neg3 {j a : ℝ} (hj : Certificate j) (ha : Certificate a) (hbin : -3 ≤ j) :
    Fcost j a ≤ 39/100 := by
  by_cases h : j < -2
  · exact (F_P hj ha ⟨hbin,h⟩).trans (by norm_num)
  by_cases h' : j < -1
  · exact (F_R hj ha ⟨le_of_not_gt h,h'⟩).trans (by norm_num)
  by_cases h'' : j < 4
  · exact (F_UV hj ha ⟨le_of_not_gt h',h''⟩).trans (by norm_num)
  exact F_T hj ha (le_of_not_gt h'')
lemma F_neg_segment {j a : ℝ} (hj : Certificate j) (ha : Certificate a)
    (hbin : -3 ≤ j ∧ j ≤ -1) (ha' : a < -1) : Fcost j a ≤ 23/100 := by
  by_cases h : j < -2
  · exact (F_P_neg hj ha ⟨hbin.1,h⟩ ha').trans (by norm_num)
  by_cases h' : j < -1
  · exact (F_R_neg hj ha ⟨le_of_not_gt h,h'⟩ ha').trans (by norm_num)
  exact F_UV hj ha ⟨le_of_not_gt h',by linarith [hbin.2]⟩

lemma Certificate.l_le {a : ℝ} (hc : Certificate a) : l a ≤ 9/100 := by
  have hL := hc.2.2.2.2.1.2.2.1
  have hL' : L a ≤ 119/100 := by
    unfold row at hL
    split_ifs at hL <;> dsimp only at hL <;> linarith
  unfold L at hL'
  linarith

lemma monotone_logq_add_sq : Monotone (fun a => logq a+a^2/2) := by
  apply monotone_of_hasDerivAt_nonneg (f' := q)
  · intro a
    convert! (hasDerivAt_logq a).add (((hasDerivAt_id a).pow 2).div_const 2) using 1
    unfold gaussianGap
    dsimp
    ring
  · intro a
    exact (gaussianHazard_pos a).le

lemma endpoint_square_bound {a c j x : ℝ} (hj : j ∈ Icc a c) (hx : x ∈ Icc a c)
    (hjneg : j ≤ 0) (hxneg : x ≤ 0) : j^2 ≤ x^2+2*delta c a := by
  have hδ : 0 ≤ delta c a := sub_nonneg.mpr (strictMono_logq.monotone (hj.1.trans hj.2))
  by_cases hjx : j ≤ x
  · have h := monotone_logq_add_sq hjx
    have hj' := strictMono_logq.monotone hj.1
    have hx' := strictMono_logq.monotone hx.2
    dsimp only [delta]
    linarith
  · have hs : (-j)^2 ≤ (-x)^2 :=
      (sq_le_sq₀ (neg_nonneg.mpr hjneg) (neg_nonneg.mpr hxneg)).mpr (by linarith)
    nlinarith only [hs,hδ]

lemma negative_chi_sq {x : ℝ} (hc : Certificate x) (hx : x ≤ -1) :
    x^2*(chi x)^2 ≤ (9/100)^2 := by
  have he : (q x-x)*chi x = l x := by
    unfold chi
    have hq : q x-x ≠ 0 := (gaussianGap_pos x).ne'
    field_simp [hq]
  have hprod := mul_nonneg (gaussianHazard_pos x).le hc.chi_nonneg
  have hlo : 0 ≤ -x*chi x := mul_nonneg (by linarith) hc.chi_nonneg
  have hhi : -x*chi x ≤ 9/100 := by nlinarith [hc.l_le]
  have hsq := (sq_le_sq₀ hlo (by norm_num : (0:ℝ) ≤ 9/100)).mpr hhi
  nlinarith only [hsq]

lemma F_O_low {a c j x : ℝ} (hcj : Certificate j) (hcx : Certificate x)
    (hj : j ∈ Icc a c) (hx : x ∈ Icc a c) (hjO : j < -3) (hxneg : x < -1) :
    Fcost j x ≤ 18/125+(11/1000)*delta c a := by
  have hs := endpoint_square_bound hj hx (by linarith) (by linarith)
  have hc2 : (chi x)^2 ≤ (7/100)^2 := sq_le_of_abs_le (by
    rw [abs_of_nonneg hcx.chi_nonneg]; exact (hcx.neg_derivatives hxneg).2.2)
  have hxc := negative_chi_sq hcx hxneg.le
  have hf := F_O_neg hcj hcx hjO hxneg
  have hδ : 0 ≤ delta c a := sub_nonneg.mpr (strictMono_logq.monotone (hj.1.trans hj.2))
  have hs' := mul_le_mul_of_nonneg_left hs (sq_nonneg (chi x))
  have hcδ := mul_le_mul_of_nonneg_left hc2 hδ
  nlinarith only [hc2,hxc,hf,hs',hcδ,hδ]

lemma F_O_high {a c j x : ℝ} (hcj : Certificate j) (hcx : Certificate x)
    (hj : j ∈ Icc a c) (hx : x ∈ Icc a c) (hjO : j < -3) (hxpos : -1 ≤ x) :
    Fcost j x ≤ 59/250+(31/1000)*delta c a := by
  have hm : (-1:ℝ) ∈ Icc a c := ⟨by linarith [hj.1],hxpos.trans hx.2⟩
  have hs := endpoint_square_bound hj hm (by linarith) (by norm_num)
  have hc2 : (chi x)^2 ≤ (97/1000)^2 := sq_le_of_abs_le (by
    rw [abs_of_nonneg hcx.chi_nonneg]; exact (hcx.pos_derivatives hxpos).2.2)
  have hf := F_O_pos hcj hcx hjO hxpos
  have hδ : 0 ≤ delta c a := sub_nonneg.mpr (strictMono_logq.monotone (hj.1.trans hj.2))
  have hs' := mul_le_mul_of_nonneg_left hs (sq_nonneg (chi x))
  have hcδ := mul_le_mul_of_nonneg_left hc2 hδ
  nlinarith only [hc2,hf,hs',hcδ,hδ]

end Submission.Obl.Entropy__two_eigenvalue_secant_deduction
