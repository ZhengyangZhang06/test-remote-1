import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace Submission.Obl.Entropy__integrated_two_eigenvalue

/-- The separation threshold in Section 4.2. -/
noncomputable def threshold (m δ : ℝ) : ℝ :=
  ((1+m)/4)*(1+δ^2/30+δ^4/1680)/(1+δ^2/36)

lemma threshold_at_zero (m : ℝ) : threshold m 0 = (1+m)/4 := by
  simp [threshold]

lemma threshold_lower (m δ : ℝ) (hm : 0 ≤ m) : (1+m)/4 ≤ threshold m δ := by
  have hd : 0 < 1+δ^2/36 := by positivity
  rw [threshold, le_div_iff₀ hd]
  have hp : 0 ≤ (1+m)*(δ^2/180+δ^4/1680) := by positivity
  nlinarith

lemma threshold_mono {m a b : ℝ} (hm : 0 ≤ m) (ha : 0 ≤ a) (hab : a ≤ b) :
    threshold m a ≤ threshold m b := by
  have ha2 : 0 ≤ a^2 := sq_nonneg a
  have hb2 : 0 ≤ b^2 := sq_nonneg b
  have hab2 : a^2 ≤ b^2 := sq_le_sq₀ ha (ha.trans hab) |>.mpr hab
  have hda : 0 < 1+a^2/36 := by positivity
  have hdb : 0 < 1+b^2/36 := by positivity
  rw [threshold, threshold, div_le_div_iff₀ hda hdb]
  have hh : 0 ≤ (1+m)*(b^2-a^2)*(1/180+(a^2+b^2)/1680+a^2*b^2/60480) := by
    apply mul_nonneg
    · exact mul_nonneg (by linarith) (sub_nonneg.mpr hab2)
    · positivity
  nlinarith [hh]

/-- The tail comparison used when the lower endpoint is below -3. -/
lemma threshold_tail {δ : ℝ} (hδ : 4 ≤ δ) :
    1/4+(13/5000)*δ^2 ≤ threshold 0 δ := by
  have hd : 0 < 1+δ^2/36 := by positivity
  rw [threshold, le_div_iff₀ hd]
  have hδ2 : 16 ≤ δ^2 := by nlinarith
  have hh := mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr hδ2)
  nlinarith [sq_nonneg δ]

lemma threshold_R {δ Pm Pp : ℝ} (hPm : Pm ≤ 59/200) (hPp : Pp ≤ 39/100) :
    max Pm ((Pm+Pp)/2) ≤ threshold (19/50) δ := by
  have ht := threshold_lower (19/50) δ (by norm_num)
  apply max_le <;> linarith

lemma threshold_UV {δ Pm Pp : ℝ} (hPm : Pm ≤ 23/100) (hPp : Pp ≤ 39/100) :
    max Pm ((Pm+Pp)/2) ≤ threshold (17/25) δ := by
  have ht := threshold_lower (17/25) δ (by norm_num)
  apply max_le <;> linarith

lemma threshold_T {δ Pm Pp : ℝ} (hPm : Pm ≤ 39/100) (hPp : Pp ≤ 39/100) :
    max Pm ((Pm+Pp)/2) ≤ threshold (17/25) δ := by
  have ht := threshold_lower (17/25) δ (by norm_num)
  apply max_le <;> linarith

lemma threshold_P_low {δ Pm Pp : ℝ} (hPm : Pm ≤ 1/5) (hPp : Pp ≤ 1/5) :
    max Pm ((Pm+Pp)/2) ≤ threshold (19/100) δ := by
  have ht := threshold_lower (19/100) δ (by norm_num)
  apply max_le <;> linarith

lemma P_increment_bound {δ c : ℝ} (hδ : 81/50 ≤ δ) (hδc : δ ≤ c) :
    (61/100-(1539/5000)/δ)^2 ≤ (61/100-(1539/5000)/c)^2 := by
  have hd : 0 < δ := by linarith
  have hc : 0 < c := lt_of_lt_of_le hd hδc
  have h0 : 0 ≤ 61/100-(1539/5000)/δ := by
    rw [sub_nonneg, div_le_iff₀ hd]
    linarith
  have hh : (1539/5000)/c ≤ (1539/5000)/δ :=
    div_le_div_of_nonneg_left (by norm_num) hd hδc
  exact (sq_le_sq₀ h0 (by linarith)).mpr (by linarith)

lemma threshold_P_middle {δ Pm Pp : ℝ} (hδ : 81/50 ≤ δ) (hδ4 : δ ≤ 4)
    (hPm : Pm ≤ (61/100-(1539/5000)/δ)^2) (hPp : Pp ≤ 23/100) :
    max Pm ((Pm+Pp)/2) ≤ threshold (19/100) δ := by
  have hb := P_increment_bound hδ hδ4
  norm_num at hb
  have ht := threshold_lower (19/100) δ (by norm_num)
  apply max_le <;> linarith

lemma threshold_P_next {δ Pm Pp : ℝ} (hδ : 4 ≤ δ) (hδ5 : δ ≤ 5)
    (hPm : Pm ≤ (61/100-(1539/5000)/δ)^2) (hPp : Pp ≤ 39/100) :
    max Pm ((Pm+Pp)/2) ≤ threshold (19/100) δ := by
  have hb := P_increment_bound (by linarith : (81:ℝ)/50 ≤ δ) hδ5
  norm_num at hb
  have ht := threshold_mono (m := (19:ℝ)/100) (by norm_num) (by norm_num) hδ
  norm_num [threshold] at ht
  unfold threshold
  norm_num
  constructor <;> linarith

lemma threshold_P_high {δ Pm Pp : ℝ} (hδ : 5 ≤ δ)
    (hPm : Pm ≤ (61/100)^2) (hPp : Pp ≤ 39/100) :
    max Pm ((Pm+Pp)/2) ≤ threshold (19/100) δ := by
  have ht := threshold_mono (m := (19:ℝ)/100) (by norm_num) (by norm_num) hδ
  norm_num [threshold] at ht
  unfold threshold
  norm_num
  constructor <;> linarith

lemma threshold_O_low {δ : ℝ} (hδ : 0 ≤ δ) :
    max ((18/125)+(11/1000)*δ) (1/5) ≤ threshold 0 δ := by
  by_cases hδ4 : δ ≤ 4
  · have ht := threshold_lower 0 δ (by norm_num)
    apply max_le <;> linarith
  · have ht := threshold_tail (le_of_lt (lt_of_not_ge hδ4))
    have hh := sq_nonneg (26*δ-55)
    apply max_le <;> nlinarith

lemma threshold_O_high {δ : ℝ} (hδ : 4 ≤ δ) :
    39/250+(31/1000)*δ-(46/125)/δ ≤ threshold 0 δ := by
  have ht := threshold_tail hδ
  have hd : 0 ≤ (46/125)/δ := by positivity
  nlinarith [sq_nonneg (26*δ-155)]

lemma threshold_O_upper {δ : ℝ} (hδ : 13/2 ≤ δ) : 39/100 ≤ threshold 0 δ := by
  have ht := threshold_mono (m := 0) (by norm_num) (by norm_num) hδ
  norm_num [threshold] at ht
  unfold threshold
  norm_num
  linarith

end Submission.Obl.Entropy__integrated_two_eigenvalue
