import Submission.Obl.Entropy__two_eigenvalue_secant_deduction.Partial

open Set

namespace Submission.Obl.Entropy__two_eigenvalue_secant_deduction
open Submission.Lib.PairEstimate

def Gaps : Prop := 81/50 < delta (-1) (-2) ∧ 4 < delta (-1) (-3) ∧
  4 < delta 4 (-2) ∧ 13/2 < delta 4 (-3)

lemma delta_le_delta {a c x y : ℝ} (ha : a ≤ x) (hc : y ≤ c) : delta y x ≤ delta c a := by
  dsimp only [delta]
  linarith [strictMono_logq.monotone ha, strictMono_logq.monotone hc]

lemma uniform_lower {a c P : ℝ} (hac : a ≤ c) (hC : ∀ x, Certificate x) (hP : 0 ≤ P)
    (hF : ∀ x ∈ Ioo a c, Fcost a x ≤ P) :
    ∀ x ∈ Icc a c, ‖J a x-J a a‖ ≤ Real.sqrt P*(logq x-logq a) := by
  intro x hx
  exact J_sub_le_open hx.1 hP (hC a).1 (fun y _ => (hC y).2.2.2.1)
    (fun y hy => hF y ⟨hy.1,hy.2.trans_le hx.2⟩)

lemma uniform_upper {a c P : ℝ} (hac : a ≤ c) (hC : ∀ x, Certificate x) (hP : 0 ≤ P)
    (hF : ∀ x ∈ Ioo a c, Fcost c x ≤ P) :
    ∀ x ∈ Icc a c, ‖J c x-J c c‖ ≤ Real.sqrt P*(logq c-logq x) := by
  intro x hx
  rw [norm_sub_rev]
  exact J_sub_le_open hx.2 hP (hC c).1 (fun y _ => (hC y).2.2.2.1)
    (fun y hy => hF y ⟨hx.1.trans_lt hy.1,hy.2⟩)

lemma partial_P {a c : ℝ} (hC : ∀ x, Certificate x) (hg : Gaps)
    (ha : -3 ≤ a ∧ a < -2) (hc : -1 < c) :
    0 ≤ 61/100-(1539/5000)/delta c a ∧
    61/100-(1539/5000)/delta c a ≤ 61/100 ∧
    (∀ x ∈ Icc a c, ‖J a x-J a a‖ ≤
      (61/100-(1539/5000)/delta c a)*(logq x-logq a)) := by
  have hac : a < c := by linarith [ha.2]
  have hcut : (-1:ℝ) ∈ Icc a c := ⟨by linarith [ha.2],hc.le⟩
  have hlen : (81:ℝ)/50 ≤ logq (-1)-logq a :=
    hg.1.le.trans (delta_le_delta ha.2.le le_rfl)
  have hd : 0 < delta c a := sub_pos.mpr (strictMono_logq hac)
  have hlenδ : (81:ℝ)/50 ≤ delta c a :=
    hlen.trans (delta_le_delta le_rfl hc.le)
  have hbetween := blend_between (A := (42:ℝ)/100) (B := 61/100)
    (by norm_num) (by norm_num : (0:ℝ) ≤ 81/50) hd hlenδ
  have he : blend (42/100) (61/100) (81/50) (delta c a) =
      61/100-(1539/5000)/delta c a := by unfold blend; ring
  rw [he] at hbetween
  refine ⟨by linarith [hbetween.1], hbetween.2, ?_⟩
  have h := partial_norm_bound (j := a) hac hcut
    (by norm_num : (42:ℝ)/100 ≤ 61/100) (by norm_num) hlen ?_ ?_
  · simpa only [he] using h
  · intro x hx
    have h := J_sub_le_open hx.1 (by positivity : (0:ℝ) ≤ (42/100)^2) (hC a).1
      (fun y _ => (hC y).2.2.2.1)
      (fun y hy => F_P_neg (hC a) (hC y) ha (hy.2.trans_le hx.2))
    simpa only [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 42/100)] using h
  · intro x hx
    have h := J_sub_le_open hx.1 (by positivity : (0:ℝ) ≤ (61/100)^2) (hC a).1
      (fun y _ => (hC y).2.2.2.1)
      (fun y hy => F_P_pos (hC a) (hC y) ha hy.1.le)
    simpa only [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 61/100)] using h

lemma partial_O {a c : ℝ} (hC : ∀ x, Certificate x) (hg : Gaps)
    (ha : a < -3) (hc : -1 < c) :
    0 ≤ 39/250+(31/1000)*delta c a-(46/125)/delta c a ∧
    (∀ x ∈ Icc a c, ‖J a x-J a a‖ ≤
      Real.sqrt (39/250+(31/1000)*delta c a-(46/125)/delta c a)*(logq x-logq a)) := by
  have hac : a < c := by linarith
  have hd : 0 < delta c a := sub_pos.mpr (strictMono_logq hac)
  have hlen : (4:ℝ) ≤ logq (-1)-logq a :=
    hg.2.1.le.trans (delta_le_delta ha.le le_rfl)
  have hlenδ : (4:ℝ) ≤ delta c a := hlen.trans (delta_le_delta le_rfl hc.le)
  have hA : 0 ≤ 18/125+(11/1000)*delta c a := by positivity
  have hAB : 18/125+(11/1000)*delta c a ≤ 59/250+(31/1000)*delta c a := by linarith
  have he : blend (18/125+(11/1000)*delta c a) (59/250+(31/1000)*delta c a) 4 (delta c a) =
      39/250+(31/1000)*delta c a-(46/125)/delta c a := by
    unfold blend
    field_simp
    <;> ring
  have hbetween := blend_between hAB (by norm_num : (0:ℝ) ≤ 4) hd hlenδ
  rw [he] at hbetween
  refine ⟨hA.trans hbetween.1, ?_⟩
  have h := partial_two_costs (j := a) hac (show (-1:ℝ) ∈ Icc a c by constructor <;> linarith)
    hA hAB (by norm_num) hlen (hC a) hC ?_ ?_
  · simpa only [he] using h
  · intro x hx
    exact F_O_low (hC a) (hC x) ⟨le_rfl,hac.le⟩ ⟨hx.1.le,by linarith [hx.2]⟩ ha hx.2
  · intro x hx
    exact F_O_high (hC a) (hC x) ⟨le_rfl,hac.le⟩ ⟨by linarith [hx.1],hx.2.le⟩ ha hx.1.le

end Submission.Obl.Entropy__two_eigenvalue_secant_deduction
