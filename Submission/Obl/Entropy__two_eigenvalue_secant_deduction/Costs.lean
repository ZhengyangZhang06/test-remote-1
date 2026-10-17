import Submission.Obl.Entropy__two_eigenvalue_secant_deduction.Increment
import Submission.Obl.Entropy__two_eigenvalue_secant_deduction.Boxes

open Set

namespace Submission.Obl.Entropy__two_eigenvalue_secant_deduction
open Submission.Lib.GaussianTransport Submission.Lib.PairEstimate

lemma Certificate.D_nonneg {j : ℝ} (h : Certificate j) : 0 ≤ D j := by
  exact div_nonneg (by norm_num) h.1.le
lemma Certificate.L_nonneg {j : ℝ} (h : Certificate j) : 0 ≤ L j := by
  have hl := h.2.2.2.1
  unfold L; positivity
lemma Certificate.J_nonneg {j : ℝ} (h : Certificate j) : 0 ≤ D j*(3/2)*b j :=
  mul_nonneg (mul_nonneg h.D_nonneg (by norm_num)) h.2.1.le
lemma Certificate.chi_nonneg {a : ℝ} (h : Certificate a) : 0 ≤ chi a :=
  div_nonneg h.2.2.2.1.le (gaussianGap_pos a).le
lemma Certificate.neg_derivatives {a : ℝ} (h : Certificate a) (ha : a < -1) :
    -(2/25) ≤ z a ∧ z a ≤ 7/10 ∧ chi a ≤ 7/100 := by
  simpa only [if_pos ha] using h.2.2.2.2.2.2.1
lemma Certificate.pos_derivatives {a : ℝ} (h : Certificate a) (ha : -1 ≤ a) :
    -(19/40) ≤ z a ∧ z a ≤ 0 ∧ chi a ≤ 97/1000 := by
  simpa only [if_neg (not_lt.mpr ha)] using h.2.2.2.2.2.2.1
lemma Certificate.hstar_bounds {a : ℝ} (h : Certificate a) :
    4/5 ≤ hstar a ∧ hstar a ≤ 177/100 := h.2.2.2.2.2.2.2

lemma Fcost_formula (j a : ℝ) : Fcost j a = (chi a)^2 *
    ((82/37)+(40/3)*(z a)^2+D j*(W j a)^2+
      ((82/37)*b j-eta/2+L j*z a+D j*E j*W j a)^2/ell j+
      (-eta+(D j*(3/2)*b j)*W j a)^2/(3/4)) := by
  unfold Fcost incrementCost D L E eta
  ring

lemma sq_le_of_abs_le {x M : ℝ} (hx : |x| ≤ M) : x^2 ≤ M^2 := by
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) ((abs_nonneg x).trans hx)).mpr hx

lemma Fcost_le_scaled {j a dm zm wm mm jm : ℝ} (hc : Certificate j)
    (hd : D j ≤ dm) (hz : |z a| ≤ zm) (hw : |W j a| ≤ wm)
    (hm : |(82/37)*b j-eta/2+L j*z a+D j*E j*W j a| ≤ mm)
    (hj : |-eta+(D j*(3/2)*b j)*W j a| ≤ jm) :
    Fcost j a ≤ (chi a)^2 * ((82/37)+(40/3)*zm^2+dm*wm^2+mm^2/ell j+jm^2/(3/4)) := by
  have hz2 := mul_le_mul_of_nonneg_left (sq_le_of_abs_le hz) (by norm_num : (0:ℝ) ≤ 40/3)
  have hw2 := mul_le_mul hd (sq_le_of_abs_le hw) (sq_nonneg _) (hc.D_nonneg.trans hd)
  have hm2 := div_le_div_of_nonneg_right (sq_le_of_abs_le hm) (ell_pos j).le
  have hj2 := div_le_div_of_nonneg_right (sq_le_of_abs_le hj) (by norm_num : (0:ℝ) ≤ 3/4)
  rw [Fcost_formula]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  linarith only [hz2,hw2,hm2,hj2]

lemma row_O {j : ℝ} (hj : j < -3) :
    row j = ((0:ℝ), (9/100:ℝ), (3/5:ℝ), (59/200)*(7+j^2), (37/100:ℝ), (14/25:ℝ), (18/25:ℝ), (13/100:ℝ)) := by
  unfold row
  split_ifs <;> first | rfl | (exfalso; linarith [hj])

lemma F_O_neg {j a : ℝ} (hcj : Certificate j) (hca : Certificate a)
    (hj : j < -3) (ha : a < -1) : Fcost j a ≤ (chi a)^2*(20+(26/25)*(7+j^2)) := by
  have hr := hcj.2.2.2.2.1
  rw [row_O hj] at hr
  dsimp only at hr
  obtain ⟨hb0,hb1,hL,hD,hK0,hK1,hJ⟩ := hr
  obtain ⟨hz0,hz1,hchi⟩ := hca.neg_derivatives ha
  have hbds := box_O_neg (b j) (L j) (D j*E j) (D j*(3/2)*b j) (z a) (hstar a)
    ⟨hb0,hb1⟩ ⟨hcj.L_nonneg,hL⟩ ⟨hK0,hK1⟩ ⟨hcj.J_nonneg,hJ⟩ ⟨by linarith only [hz0],hz1⟩ hca.hstar_bounds
  have hz : |z a| ≤ (7/10:ℝ) := abs_le.mpr ⟨by linarith only [hz0], by linarith only [hz1]⟩
  have hcost := Fcost_le_scaled hcj hD hz
    (by simpa only [W, mul_assoc] using hbds.1)
    (by simpa only [W, mul_assoc] using hbds.2.1)
    (by simpa only [W, mul_assoc] using hbds.2.2)
  have hell : ell j = (13/100:ℝ) := by unfold ell; rw [row_O hj]
  rw [hell] at hcost
  refine hcost.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
  nlinarith [sq_nonneg j]

lemma F_O_pos {j a : ℝ} (hcj : Certificate j) (hca : Certificate a)
    (hj : j < -3) (ha : -1 ≤ a) : Fcost j a ≤ (chi a)^2*(12+(163/100)*(7+j^2)) := by
  have hr := hcj.2.2.2.2.1
  rw [row_O hj] at hr
  dsimp only at hr
  obtain ⟨hb0,hb1,hL,hD,hK0,hK1,hJ⟩ := hr
  obtain ⟨hz0,hz1,hchi⟩ := hca.pos_derivatives ha
  have hbds := box_O_pos (b j) (L j) (D j*E j) (D j*(3/2)*b j) (z a) (hstar a)
    ⟨hb0,hb1⟩ ⟨hcj.L_nonneg,hL⟩ ⟨hK0,hK1⟩ ⟨hcj.J_nonneg,hJ⟩ ⟨by linarith only [hz0],hz1⟩ hca.hstar_bounds
  have hz : |z a| ≤ (19/40:ℝ) := abs_le.mpr ⟨by linarith only [hz0], by linarith only [hz1]⟩
  have hcost := Fcost_le_scaled hcj hD hz
    (by simpa only [W, mul_assoc] using hbds.1)
    (by simpa only [W, mul_assoc] using hbds.2.1)
    (by simpa only [W, mul_assoc] using hbds.2.2)
  have hell : ell j = (13/100:ℝ) := by unfold ell; rw [row_O hj]
  rw [hell] at hcost
  refine hcost.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
  nlinarith [sq_nonneg j]

lemma row_P {j : ℝ} (hj : -3 ≤ j ∧ j < -2) :
    row j = ((83/1000:ℝ), (3/20:ℝ), (101/100:ℝ), (43/10:ℝ), (29/100:ℝ), (23/50:ℝ), (18/25:ℝ), (13/100:ℝ)) := by
  unfold row
  split_ifs <;> first | rfl | (exfalso; linarith [hj])

lemma F_P_neg {j a : ℝ} (hcj : Certificate j) (hca : Certificate a)
    (hj : -3 ≤ j ∧ j < -2) (ha : a < -1) : Fcost j a ≤ (42/100:ℝ)^2 := by
  have hr := hcj.2.2.2.2.1
  rw [row_P hj] at hr
  dsimp only at hr
  obtain ⟨hb0,hb1,hL,hD,hK0,hK1,hJ⟩ := hr
  obtain ⟨hz0,hz1,hchi⟩ := hca.neg_derivatives ha
  have hbds := box_P_neg (b j) (L j) (D j*E j) (D j*(3/2)*b j) (z a) (hstar a)
    ⟨hb0,hb1⟩ ⟨hcj.L_nonneg,hL⟩ ⟨hK0,hK1⟩ ⟨hcj.J_nonneg,hJ⟩ ⟨by linarith only [hz0],hz1⟩ hca.hstar_bounds
  have hz : |z a| ≤ (7/10:ℝ) := abs_le.mpr ⟨by linarith only [hz0], by linarith only [hz1]⟩
  have hcost := Fcost_le_scaled hcj hD hz
    (by simpa only [W, mul_assoc] using hbds.1)
    (by simpa only [W, mul_assoc] using hbds.2.1)
    (by simpa only [W, mul_assoc] using hbds.2.2)
  have hell : ell j = (13/100:ℝ) := by unfold ell; rw [row_P hj]
  rw [hell] at hcost
  have hc2 : (chi a)^2 ≤ (7/100:ℝ)^2 := sq_le_of_abs_le (by
    rw [abs_of_nonneg hca.chi_nonneg]; exact hchi)
  norm_num at hcost hc2 ⊢
  nlinarith only [hcost,hc2]

lemma F_P_pos {j a : ℝ} (hcj : Certificate j) (hca : Certificate a)
    (hj : -3 ≤ j ∧ j < -2) (ha : -1 ≤ a) : Fcost j a ≤ (61/100:ℝ)^2 := by
  have hr := hcj.2.2.2.2.1
  rw [row_P hj] at hr
  dsimp only at hr
  obtain ⟨hb0,hb1,hL,hD,hK0,hK1,hJ⟩ := hr
  obtain ⟨hz0,hz1,hchi⟩ := hca.pos_derivatives ha
  have hbds := box_P_pos (b j) (L j) (D j*E j) (D j*(3/2)*b j) (z a) (hstar a)
    ⟨hb0,hb1⟩ ⟨hcj.L_nonneg,hL⟩ ⟨hK0,hK1⟩ ⟨hcj.J_nonneg,hJ⟩ ⟨by linarith only [hz0],hz1⟩ hca.hstar_bounds
  have hz : |z a| ≤ (19/40:ℝ) := abs_le.mpr ⟨by linarith only [hz0], by linarith only [hz1]⟩
  have hcost := Fcost_le_scaled hcj hD hz
    (by simpa only [W, mul_assoc] using hbds.1)
    (by simpa only [W, mul_assoc] using hbds.2.1)
    (by simpa only [W, mul_assoc] using hbds.2.2)
  have hell : ell j = (13/100:ℝ) := by unfold ell; rw [row_P hj]
  rw [hell] at hcost
  have hc2 : (chi a)^2 ≤ (97/1000:ℝ)^2 := sq_le_of_abs_le (by
    rw [abs_of_nonneg hca.chi_nonneg]; exact hchi)
  norm_num at hcost hc2 ⊢
  nlinarith only [hcost,hc2]

lemma row_R {j : ℝ} (hj : -2 ≤ j ∧ j < -1) :
    row j = ((7/50:ℝ), (23/100:ℝ), (119/100:ℝ), (3:ℝ), (29/100:ℝ), (371/1000:ℝ), (17/25:ℝ), (13/100:ℝ)) := by
  unfold row
  split_ifs <;> first | rfl | (exfalso; linarith [hj])

lemma F_R_neg {j a : ℝ} (hcj : Certificate j) (hca : Certificate a)
    (hj : -2 ≤ j ∧ j < -1) (ha : a < -1) : Fcost j a ≤ (1/5:ℝ) := by
  have hr := hcj.2.2.2.2.1
  rw [row_R hj] at hr
  dsimp only at hr
  obtain ⟨hb0,hb1,hL,hD,hK0,hK1,hJ⟩ := hr
  obtain ⟨hz0,hz1,hchi⟩ := hca.neg_derivatives ha
  have hbds := box_R_neg (b j) (L j) (D j*E j) (D j*(3/2)*b j) (z a) (hstar a)
    ⟨hb0,hb1⟩ ⟨hcj.L_nonneg,hL⟩ ⟨hK0,hK1⟩ ⟨hcj.J_nonneg,hJ⟩ ⟨by linarith only [hz0],hz1⟩ hca.hstar_bounds
  have hz : |z a| ≤ (7/10:ℝ) := abs_le.mpr ⟨by linarith only [hz0], by linarith only [hz1]⟩
  have hcost := Fcost_le_scaled hcj hD hz
    (by simpa only [W, mul_assoc] using hbds.1)
    (by simpa only [W, mul_assoc] using hbds.2.1)
    (by simpa only [W, mul_assoc] using hbds.2.2)
  have hell : ell j = (13/100:ℝ) := by unfold ell; rw [row_R hj]
  rw [hell] at hcost
  have hc2 : (chi a)^2 ≤ (7/100:ℝ)^2 := sq_le_of_abs_le (by
    rw [abs_of_nonneg hca.chi_nonneg]; exact hchi)
  norm_num at hcost hc2 ⊢
  nlinarith only [hcost,hc2]

lemma F_R_pos {j a : ℝ} (hcj : Certificate j) (hca : Certificate a)
    (hj : -2 ≤ j ∧ j < -1) (ha : -1 ≤ a) : Fcost j a ≤ (59/200:ℝ) := by
  have hr := hcj.2.2.2.2.1
  rw [row_R hj] at hr
  dsimp only at hr
  obtain ⟨hb0,hb1,hL,hD,hK0,hK1,hJ⟩ := hr
  obtain ⟨hz0,hz1,hchi⟩ := hca.pos_derivatives ha
  have hbds := box_R_pos (b j) (L j) (D j*E j) (D j*(3/2)*b j) (z a) (hstar a)
    ⟨hb0,hb1⟩ ⟨hcj.L_nonneg,hL⟩ ⟨hK0,hK1⟩ ⟨hcj.J_nonneg,hJ⟩ ⟨by linarith only [hz0],hz1⟩ hca.hstar_bounds
  have hz : |z a| ≤ (19/40:ℝ) := abs_le.mpr ⟨by linarith only [hz0], by linarith only [hz1]⟩
  have hcost := Fcost_le_scaled hcj hD hz
    (by simpa only [W, mul_assoc] using hbds.1)
    (by simpa only [W, mul_assoc] using hbds.2.1)
    (by simpa only [W, mul_assoc] using hbds.2.2)
  have hell : ell j = (13/100:ℝ) := by unfold ell; rw [row_R hj]
  rw [hell] at hcost
  have hc2 : (chi a)^2 ≤ (97/1000:ℝ)^2 := sq_le_of_abs_le (by
    rw [abs_of_nonneg hca.chi_nonneg]; exact hchi)
  norm_num at hcost hc2 ⊢
  nlinarith only [hcost,hc2]

lemma row_U {j : ℝ} (hj : -1 ≤ j ∧ j < 1/2) :
    row j = ((11/50:ℝ), (171/500:ℝ), (119/100:ℝ), (43/25:ℝ), (29/100:ℝ), (199/500:ℝ), (61/100:ℝ), (123/1000:ℝ)) := by
  unfold row
  split_ifs <;> first | rfl | (exfalso; linarith [hj])

lemma F_U_neg {j a : ℝ} (hcj : Certificate j) (hca : Certificate a)
    (hj : -1 ≤ j ∧ j < 1/2) (ha : a < -1) : Fcost j a ≤ (23/100:ℝ) := by
  have hr := hcj.2.2.2.2.1
  rw [row_U hj] at hr
  dsimp only at hr
  obtain ⟨hb0,hb1,hL,hD,hK0,hK1,hJ⟩ := hr
  obtain ⟨hz0,hz1,hchi⟩ := hca.neg_derivatives ha
  have hbds := box_U_neg (b j) (L j) (D j*E j) (D j*(3/2)*b j) (z a) (hstar a)
    ⟨hb0,hb1⟩ ⟨hcj.L_nonneg,hL⟩ ⟨hK0,hK1⟩ ⟨hcj.J_nonneg,hJ⟩ ⟨by linarith only [hz0],hz1⟩ hca.hstar_bounds
  have hz : |z a| ≤ (7/10:ℝ) := abs_le.mpr ⟨by linarith only [hz0], by linarith only [hz1]⟩
  have hcost := Fcost_le_scaled hcj hD hz
    (by simpa only [W, mul_assoc] using hbds.1)
    (by simpa only [W, mul_assoc] using hbds.2.1)
    (by simpa only [W, mul_assoc] using hbds.2.2)
  have hell : ell j = (123/1000:ℝ) := by unfold ell; rw [row_U hj]
  rw [hell] at hcost
  have hc2 : (chi a)^2 ≤ (7/100:ℝ)^2 := sq_le_of_abs_le (by
    rw [abs_of_nonneg hca.chi_nonneg]; exact hchi)
  norm_num at hcost hc2 ⊢
  nlinarith only [hcost,hc2]

lemma F_U_pos {j a : ℝ} (hcj : Certificate j) (hca : Certificate a)
    (hj : -1 ≤ j ∧ j < 1/2) (ha : -1 ≤ a) : Fcost j a ≤ (23/100:ℝ) := by
  have hr := hcj.2.2.2.2.1
  rw [row_U hj] at hr
  dsimp only at hr
  obtain ⟨hb0,hb1,hL,hD,hK0,hK1,hJ⟩ := hr
  obtain ⟨hz0,hz1,hchi⟩ := hca.pos_derivatives ha
  have hbds := box_U_pos (b j) (L j) (D j*E j) (D j*(3/2)*b j) (z a) (hstar a)
    ⟨hb0,hb1⟩ ⟨hcj.L_nonneg,hL⟩ ⟨hK0,hK1⟩ ⟨hcj.J_nonneg,hJ⟩ ⟨by linarith only [hz0],hz1⟩ hca.hstar_bounds
  have hz : |z a| ≤ (19/40:ℝ) := abs_le.mpr ⟨by linarith only [hz0], by linarith only [hz1]⟩
  have hcost := Fcost_le_scaled hcj hD hz
    (by simpa only [W, mul_assoc] using hbds.1)
    (by simpa only [W, mul_assoc] using hbds.2.1)
    (by simpa only [W, mul_assoc] using hbds.2.2)
  have hell : ell j = (123/1000:ℝ) := by unfold ell; rw [row_U hj]
  rw [hell] at hcost
  have hc2 : (chi a)^2 ≤ (97/1000:ℝ)^2 := sq_le_of_abs_le (by
    rw [abs_of_nonneg hca.chi_nonneg]; exact hchi)
  norm_num at hcost hc2 ⊢
  nlinarith only [hcost,hc2]

lemma row_V {j : ℝ} (hj : 1/2 ≤ j ∧ j < 4) :
    row j = ((337/1000:ℝ), (9/20:ℝ), (83/100:ℝ), (87/100:ℝ), (31/100:ℝ), (2/5:ℝ), (1/2:ℝ), (3/50:ℝ)) := by
  unfold row
  split_ifs <;> first | rfl | (exfalso; linarith [hj])

lemma F_V_neg {j a : ℝ} (hcj : Certificate j) (hca : Certificate a)
    (hj : 1/2 ≤ j ∧ j < 4) (ha : a < -1) : Fcost j a ≤ (23/100:ℝ) := by
  have hr := hcj.2.2.2.2.1
  rw [row_V hj] at hr
  dsimp only at hr
  obtain ⟨hb0,hb1,hL,hD,hK0,hK1,hJ⟩ := hr
  obtain ⟨hz0,hz1,hchi⟩ := hca.neg_derivatives ha
  have hbds := box_V_neg (b j) (L j) (D j*E j) (D j*(3/2)*b j) (z a) (hstar a)
    ⟨hb0,hb1⟩ ⟨hcj.L_nonneg,hL⟩ ⟨hK0,hK1⟩ ⟨hcj.J_nonneg,hJ⟩ ⟨by linarith only [hz0],hz1⟩ hca.hstar_bounds
  have hz : |z a| ≤ (7/10:ℝ) := abs_le.mpr ⟨by linarith only [hz0], by linarith only [hz1]⟩
  have hcost := Fcost_le_scaled hcj hD hz
    (by simpa only [W, mul_assoc] using hbds.1)
    (by simpa only [W, mul_assoc] using hbds.2.1)
    (by simpa only [W, mul_assoc] using hbds.2.2)
  have hell : ell j = (3/50:ℝ) := by unfold ell; rw [row_V hj]
  rw [hell] at hcost
  have hc2 : (chi a)^2 ≤ (7/100:ℝ)^2 := sq_le_of_abs_le (by
    rw [abs_of_nonneg hca.chi_nonneg]; exact hchi)
  norm_num at hcost hc2 ⊢
  nlinarith only [hcost,hc2]

lemma F_V_pos {j a : ℝ} (hcj : Certificate j) (hca : Certificate a)
    (hj : 1/2 ≤ j ∧ j < 4) (ha : -1 ≤ a) : Fcost j a ≤ (23/100:ℝ) := by
  have hr := hcj.2.2.2.2.1
  rw [row_V hj] at hr
  dsimp only at hr
  obtain ⟨hb0,hb1,hL,hD,hK0,hK1,hJ⟩ := hr
  obtain ⟨hz0,hz1,hchi⟩ := hca.pos_derivatives ha
  have hbds := box_V_pos (b j) (L j) (D j*E j) (D j*(3/2)*b j) (z a) (hstar a)
    ⟨hb0,hb1⟩ ⟨hcj.L_nonneg,hL⟩ ⟨hK0,hK1⟩ ⟨hcj.J_nonneg,hJ⟩ ⟨by linarith only [hz0],hz1⟩ hca.hstar_bounds
  have hz : |z a| ≤ (19/40:ℝ) := abs_le.mpr ⟨by linarith only [hz0], by linarith only [hz1]⟩
  have hcost := Fcost_le_scaled hcj hD hz
    (by simpa only [W, mul_assoc] using hbds.1)
    (by simpa only [W, mul_assoc] using hbds.2.1)
    (by simpa only [W, mul_assoc] using hbds.2.2)
  have hell : ell j = (3/50:ℝ) := by unfold ell; rw [row_V hj]
  rw [hell] at hcost
  have hc2 : (chi a)^2 ≤ (97/1000:ℝ)^2 := sq_le_of_abs_le (by
    rw [abs_of_nonneg hca.chi_nonneg]; exact hchi)
  norm_num at hcost hc2 ⊢
  nlinarith only [hcost,hc2]

lemma row_T {j : ℝ} (hj : 4 ≤ j) :
    row j = ((89/200:ℝ), (1/2:ℝ), (1/5:ℝ), (16/25:ℝ), (8/25:ℝ), (2/5:ℝ), (12/25:ℝ), (11/500:ℝ)) := by
  unfold row
  split_ifs <;> first | rfl | (exfalso; linarith [hj])

lemma F_T_neg {j a : ℝ} (hcj : Certificate j) (hca : Certificate a)
    (hj : 4 ≤ j) (ha : a < -1) : Fcost j a ≤ (39/100:ℝ) := by
  have hr := hcj.2.2.2.2.1
  rw [row_T hj] at hr
  dsimp only at hr
  obtain ⟨hb0,hb1,hL,hD,hK0,hK1,hJ⟩ := hr
  obtain ⟨hz0,hz1,hchi⟩ := hca.neg_derivatives ha
  have hbds := box_T_neg (b j) (L j) (D j*E j) (D j*(3/2)*b j) (z a) (hstar a)
    ⟨hb0,hb1⟩ ⟨hcj.L_nonneg,hL⟩ ⟨hK0,hK1⟩ ⟨hcj.J_nonneg,hJ⟩ ⟨by linarith only [hz0],hz1⟩ hca.hstar_bounds
  have hz : |z a| ≤ (7/10:ℝ) := abs_le.mpr ⟨by linarith only [hz0], by linarith only [hz1]⟩
  have hcost := Fcost_le_scaled hcj hD hz
    (by simpa only [W, mul_assoc] using hbds.1)
    (by simpa only [W, mul_assoc] using hbds.2.1)
    (by simpa only [W, mul_assoc] using hbds.2.2)
  have hell : ell j = (11/500:ℝ) := by unfold ell; rw [row_T hj]
  rw [hell] at hcost
  have hc2 : (chi a)^2 ≤ (7/100:ℝ)^2 := sq_le_of_abs_le (by
    rw [abs_of_nonneg hca.chi_nonneg]; exact hchi)
  norm_num at hcost hc2 ⊢
  nlinarith only [hcost,hc2]

lemma F_T_pos {j a : ℝ} (hcj : Certificate j) (hca : Certificate a)
    (hj : 4 ≤ j) (ha : -1 ≤ a) : Fcost j a ≤ (39/100:ℝ) := by
  have hr := hcj.2.2.2.2.1
  rw [row_T hj] at hr
  dsimp only at hr
  obtain ⟨hb0,hb1,hL,hD,hK0,hK1,hJ⟩ := hr
  obtain ⟨hz0,hz1,hchi⟩ := hca.pos_derivatives ha
  have hbds := box_T_pos (b j) (L j) (D j*E j) (D j*(3/2)*b j) (z a) (hstar a)
    ⟨hb0,hb1⟩ ⟨hcj.L_nonneg,hL⟩ ⟨hK0,hK1⟩ ⟨hcj.J_nonneg,hJ⟩ ⟨by linarith only [hz0],hz1⟩ hca.hstar_bounds
  have hz : |z a| ≤ (19/40:ℝ) := abs_le.mpr ⟨by linarith only [hz0], by linarith only [hz1]⟩
  have hcost := Fcost_le_scaled hcj hD hz
    (by simpa only [W, mul_assoc] using hbds.1)
    (by simpa only [W, mul_assoc] using hbds.2.1)
    (by simpa only [W, mul_assoc] using hbds.2.2)
  have hell : ell j = (11/500:ℝ) := by unfold ell; rw [row_T hj]
  rw [hell] at hcost
  have hc2 : (chi a)^2 ≤ (97/1000:ℝ)^2 := sq_le_of_abs_le (by
    rw [abs_of_nonneg hca.chi_nonneg]; exact hchi)
  norm_num at hcost hc2 ⊢
  nlinarith only [hcost,hc2]

end Submission.Obl.Entropy__two_eigenvalue_secant_deduction
