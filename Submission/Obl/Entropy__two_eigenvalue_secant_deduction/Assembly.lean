import Submission.Obl.Entropy__two_eigenvalue_secant_deduction.Cases

open Set

namespace Submission.Obl.Entropy__two_eigenvalue_secant_deduction
open Submission.Lib.PairEstimate

lemma m0_P {a : ℝ} (ha : -3 ≤ a ∧ a < -2) : m0 a = 19/100 := by
  unfold m0; split_ifs <;> norm_num <;> linarith [ha]
lemma m0_R {a : ℝ} (ha : -2 ≤ a ∧ a < -1) : m0 a = 19/50 := by
  unfold m0; split_ifs <;> norm_num <;> linarith [ha]
lemma m0_ge_neg1 {a : ℝ} (ha : -1 ≤ a) : m0 a = 17/25 := by
  unfold m0; split_ifs <;> norm_num <;> linarith

lemma pair_uniform {a c Pm Pp : ℝ} (hac : a < c) (hC : ∀ x, Certificate x)
    (hPm : 0 ≤ Pm) (hPp : 0 ≤ Pp)
    (hm : ∀ x ∈ Ioo a c, Fcost a x ≤ Pm)
    (hp : ∀ x ∈ Ioo a c, Fcost c x ≤ Pp)
    (ht : max Pm ((Pm+Pp)/2) ≤ threshold (m0 a) (delta c a)) (G g Z : ℝ) :
    (H a c G g Z+H c a G g Z)/2 ≤ Q G (g-G/2)+sigma a c*Z^2 :=
  pair_of_partial_bounds hac (hC a) (hC c) hPm hPp
    (uniform_lower hac.le hC hPm hm) (uniform_upper hac.le hC hPp hp) ht G g Z

lemma pair_ge_neg2 {a c : ℝ} (hac : a < c) (ha : -2 ≤ a) (hC : ∀ x, Certificate x)
    (G g Z : ℝ) : (H a c G g Z+H c a G g Z)/2 ≤ Q G (g-G/2)+sigma a c*Z^2 := by
  by_cases ha1 : a < -1
  · apply pair_uniform (Pm := 59/200) (Pp := 39/100) hac hC (by norm_num) (by norm_num)
    · intro x _; exact F_R (hC a) (hC x) ⟨ha,ha1⟩
    · intro x _; exact F_ge_neg3 (hC c) (hC x) (by linarith)
    · rw [m0_R ⟨ha,ha1⟩]
      exact threshold_R le_rfl le_rfl
  by_cases ha4 : a < 4
  · apply pair_uniform (Pm := 23/100) (Pp := 39/100) hac hC (by norm_num) (by norm_num)
    · intro x _; exact F_UV (hC a) (hC x) ⟨le_of_not_gt ha1,ha4⟩
    · intro x _; exact F_ge_neg3 (hC c) (hC x) (by linarith)
    · rw [m0_ge_neg1 (le_of_not_gt ha1)]
      exact threshold_UV le_rfl le_rfl
  · apply pair_uniform (Pm := 39/100) (Pp := 39/100) hac hC (by norm_num) (by norm_num)
    · intro x _; exact F_T (hC a) (hC x) (le_of_not_gt ha4)
    · intro x _; exact F_T (hC c) (hC x) (by linarith)
    · rw [m0_ge_neg1 (le_of_not_gt ha1)]
      exact threshold_T le_rfl le_rfl

lemma pair_P {a c : ℝ} (hac : a < c) (ha : -3 ≤ a ∧ a < -2)
    (hC : ∀ x, Certificate x) (hg : Gaps) (G g Z : ℝ) :
    (H a c G g Z+H c a G g Z)/2 ≤ Q G (g-G/2)+sigma a c*Z^2 := by
  by_cases hc : c ≤ -1
  · apply pair_uniform (Pm := 23/100) (Pp := 23/100) hac hC (by norm_num) (by norm_num)
    · intro x hx
      exact (F_P_neg (hC a) (hC x) ha (hx.2.trans_le hc)).trans (by norm_num)
    · intro x hx
      exact F_neg_segment (hC c) (hC x) ⟨by linarith [ha.1],hc⟩ (hx.2.trans_le hc)
    · rw [m0_P ha]
      have h := threshold_lower (19/100) (delta c a) (by norm_num)
      apply max_le <;> linarith only [h]
  have hc' : -1 < c := lt_of_not_ge hc
  obtain ⟨hcoef0,hcoef1,hm⟩ := partial_P hC hg ha hc'
  have hm' : ∀ x ∈ Icc a c, ‖J a x-J a a‖ ≤
      Real.sqrt ((61/100-(1539/5000)/delta c a)^2)*(logq x-logq a) := by
    simpa only [Real.sqrt_sq hcoef0] using hm
  have hδ : (81:ℝ)/50 ≤ delta c a :=
    hg.1.le.trans (delta_le_delta ha.2.le hc'.le)
  by_cases hδ4 : delta c a ≤ 4
  · have hc4 : c < 4 := by
      by_contra hn
      have h := hg.2.2.1.trans_le (delta_le_delta ha.2.le (le_of_not_gt hn))
      linarith
    apply pair_of_partial_bounds (Pm := (61/100-(1539/5000)/delta c a)^2) (Pp := 23/100)
      hac (hC a) (hC c) (sq_nonneg _) (by norm_num) hm'
    · exact uniform_upper hac.le hC (by norm_num)
        (fun x _ => F_UV (hC c) (hC x) ⟨hc'.le,hc4⟩)
    · rw [m0_P ha]
      exact threshold_P_middle hδ hδ4 le_rfl le_rfl
  · apply pair_of_partial_bounds (Pm := (61/100-(1539/5000)/delta c a)^2) (Pp := 39/100)
      hac (hC a) (hC c) (sq_nonneg _) (by norm_num) hm'
    · exact uniform_upper hac.le hC (by norm_num)
        (fun x _ => F_ge_neg3 (hC c) (hC x) (by linarith))
    · rw [m0_P ha]
      by_cases hδ5 : delta c a ≤ 5
      · exact threshold_P_next (lt_of_not_ge hδ4).le hδ5 le_rfl le_rfl
      · exact threshold_P_high (lt_of_not_ge hδ5).le
          ((sq_le_sq₀ hcoef0 (by norm_num)).mpr hcoef1) le_rfl

lemma pair_O_low {a c : ℝ} (hac : a < c) (ha : a < -3) (hc : c ≤ -1)
    (hC : ∀ x, Certificate x) (G g Z : ℝ) :
    (H a c G g Z+H c a G g Z)/2 ≤ Q G (g-G/2)+sigma a c*Z^2 := by
  have hd : 0 ≤ delta c a := (sub_pos.mpr (strictMono_logq hac)).le
  let Pm := (18/125)+(11/1000)*delta c a
  have hPm : 0 ≤ Pm := by dsimp only [Pm]; positivity
  have hPp : 0 ≤ max Pm (23/100) := hPm.trans (le_max_left _ _)
  apply pair_uniform (Pm := Pm) (Pp := max Pm (23/100)) hac hC hPm hPp
  · intro x hx
    exact F_O_low (hC a) (hC x) ⟨le_rfl,hac.le⟩ ⟨hx.1.le,hx.2.le⟩ ha (hx.2.trans_le hc)
  · intro x hx
    by_cases hcO : c < -3
    · exact (F_O_low (hC c) (hC x) ⟨hac.le,le_rfl⟩ ⟨hx.1.le,hx.2.le⟩ hcO
        (hx.2.trans_le hc)).trans (le_max_left _ _)
    · exact (F_neg_segment (hC c) (hC x) ⟨le_of_not_gt hcO,hc⟩
        (hx.2.trans_le hc)).trans (le_max_right _ _)
  · simp only [m0, if_pos ha]
    have h1 : Pm ≤ threshold 0 (delta c a) :=
      (le_max_left _ _).trans (threshold_O_low hd)
    have h2 : (23:ℝ)/100 ≤ threshold 0 (delta c a) := by
      have h := threshold_lower 0 (delta c a) (by norm_num)
      linarith only [h]
    have h3 := max_le h1 h2
    apply max_le <;> linarith only [h1,h3]

lemma pair_O_high {a c : ℝ} (hac : a < c) (ha : a < -3) (hc : -1 < c)
    (hC : ∀ x, Certificate x) (hg : Gaps) (G g Z : ℝ) :
    (H a c G g Z+H c a G g Z)/2 ≤ Q G (g-G/2)+sigma a c*Z^2 := by
  obtain ⟨hPm,hm⟩ := partial_O hC hg ha hc
  have hd : (4:ℝ) ≤ delta c a := hg.2.1.le.trans (delta_le_delta ha.le hc.le)
  have hPmT := threshold_O_high hd
  by_cases hc4 : c < 4
  · apply pair_of_partial_bounds (Pm := 39/250+(31/1000)*delta c a-(46/125)/delta c a)
      (Pp := 23/100) hac (hC a) (hC c) hPm (by norm_num) hm
    · exact uniform_upper hac.le hC (by norm_num)
        (fun x _ => F_UV (hC c) (hC x) ⟨hc.le,hc4⟩)
    · simp only [m0, if_pos ha]
      have hp : (23:ℝ)/100 ≤ threshold 0 (delta c a) := by
        have h := threshold_lower 0 (delta c a) (by norm_num)
        linarith only [h]
      apply max_le <;> linarith only [hPmT,hp]
  · apply pair_of_partial_bounds (Pm := 39/250+(31/1000)*delta c a-(46/125)/delta c a)
      (Pp := 39/100) hac (hC a) (hC c) hPm (by norm_num) hm
    · exact uniform_upper hac.le hC (by norm_num)
        (fun x _ => F_T (hC c) (hC x) (le_of_not_gt hc4))
    · simp only [m0, if_pos ha]
      have hδ : (13:ℝ)/2 ≤ delta c a :=
        hg.2.2.2.le.trans (delta_le_delta ha.le (le_of_not_gt hc4))
      have hp := threshold_O_upper hδ
      apply max_le <;> linarith only [hPmT,hp]

lemma ordered_pair {a c : ℝ} (hac : a < c) (hC : ∀ x, Certificate x) (hg : Gaps)
    (G g Z : ℝ) : (H a c G g Z+H c a G g Z)/2 ≤ Q G (g-G/2)+sigma a c*Z^2 := by
  by_cases ha : a < -3
  · by_cases hc : c ≤ -1
    · exact pair_O_low hac ha hc hC G g Z
    · exact pair_O_high hac ha (lt_of_not_ge hc) hC hg G g Z
  by_cases ha2 : a < -2
  · exact pair_P hac ⟨le_of_not_gt ha,ha2⟩ hC hg G g Z
  · exact pair_ge_neg2 hac (le_of_not_gt ha2) hC G g Z

lemma all_pairs (hC : ∀ x, Certificate x) (hg : Gaps) (a c G g Z : ℝ) :
    (H a c G g Z+H c a G g Z)/2 ≤ Q G (g-G/2)+sigma a c*Z^2 := by
  rcases lt_trichotomy a c with h | h | h
  · exact ordered_pair h hC hg G g Z
  · subst c; exact diagonal a G g Z (hC a)
  · have hp := ordered_pair h hC hg G g Z
    rw [sigma_symm c a] at hp
    linarith only [hp]

/-- The endpoint expression with the division placed exactly as in the frozen statement. -/
noncomputable def rawH (a c G g Z : ℝ) :=
  (40/37)*(G*b c+Z*dk a c-(7/25)*g)^2 +
  (42/37)*(G*b c+Z*dk a c-(3/4)*g)^2 + (27/592)*g^2 +
  (40/3)*(G*l c+Z*db a c)^2 + (5/17)*(G*e c+Z*psi a c+(3/2)*g*b c)^2/p c

lemma rawH_eq (a c G g Z : ℝ) : rawH a c G g Z = H a c G g Z := by
  unfold rawH H endpointCost
  ring

end Submission.Obl.Entropy__two_eigenvalue_secant_deduction
