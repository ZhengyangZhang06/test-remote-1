import Submission.Obl.Entropy__two_eigenvalue_secant_deduction.Basic

namespace Submission.Obl.Entropy__two_eigenvalue_secant_deduction

lemma affine_le {A B x lo hi M : ℝ} (hx : lo ≤ x ∧ x ≤ hi)
    (hl : A*lo+B ≤ M) (hh : A*hi+B ≤ M) : A*x+B ≤ M := by
  by_cases hA : 0 ≤ A
  · nlinarith [mul_nonneg hA (sub_nonneg.mpr hx.2)]
  · nlinarith [mul_nonneg (le_of_lt (neg_pos.mpr (lt_of_not_ge hA))) (sub_nonneg.mpr hx.1)]

lemma mul_box {x y M lo hi : ℝ} (hx : 0 ≤ x ∧ x ≤ M) (hy : lo ≤ y ∧ y ≤ hi)
    (hlo : lo ≤ 0) (hhi : 0 ≤ hi) : M*lo ≤ x*y ∧ x*y ≤ M*hi := by
  constructor
  · nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hy.1),
      mul_nonneg (sub_nonneg.mpr hx.2) (neg_nonneg.mpr hlo)]
  · nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hy.2),
      mul_nonneg (sub_nonneg.mpr hx.2) hhi]

lemma middle_abs {β v h K lo hi M : ℝ} (hK : lo ≤ K ∧ K ≤ hi)
    (hlo : |(82/37)*β-eta/2+v+lo*(h-2*β-2*v)| ≤ M)
    (hhi : |(82/37)*β-eta/2+v+hi*(h-2*β-2*v)| ≤ M) :
    |(82/37)*β-eta/2+v+K*(h-2*β-2*v)| ≤ M := by
  rw [abs_le] at *
  constructor
  · have h := affine_le (M := M) (A := -(h-2*β-2*v)) (B := -((82/37)*β-eta/2+v)) hK
      (by linarith [hlo.1]) (by linarith [hhi.1])
    linarith only [h]
  · have h := affine_le (M := M) (A := h-2*β-2*v) (B := (82/37)*β-eta/2+v) hK
      (by linarith [hlo.2]) (by linarith [hhi.2])
    linarith only [h]

lemma box_O_neg (β Λ K J ζ h : ℝ)
    (hb : (0:ℝ) ≤ β ∧ β ≤ (9/100:ℝ))
    (hL : 0 ≤ Λ ∧ Λ ≤ (3/5:ℝ)) (hK : (37/100:ℝ) ≤ K ∧ K ≤ (14/25:ℝ))
    (hJ : 0 ≤ J ∧ J ≤ (18/25:ℝ)) (hz : (-2/25:ℝ) ≤ ζ ∧ ζ ≤ (7/10:ℝ))
    (hh : (4/5:ℝ) ≤ h ∧ h ≤ 177/100) :
    |h-2*β-2*Λ*ζ| ≤ (1867/1000:ℝ) ∧
    |(82/37)*β-eta/2+Λ*ζ+K*(h-2*β-2*Λ*ζ)| ≤ (13/25:ℝ) ∧
    |-eta+J*(h-2*β-2*Λ*ζ)| ≤ (657/500:ℝ) := by
  obtain ⟨hv0,hv1⟩ := mul_box hL hz (by norm_num) (by norm_num)
  norm_num at hv0 hv1
  have hw0 : (-11/50:ℝ) ≤ h-2*β-2*Λ*ζ := by linarith only [hb.2, hh.1, hv1]
  have hw1 : h-2*β-2*Λ*ζ ≤ (933/500:ℝ) := by linarith only [hb.1, hh.2, hv0]
  refine ⟨abs_le.mpr ⟨by linarith only [hw0], by linarith only [hw1]⟩, ?_, ?_⟩
  · simp only [mul_assoc]
    apply middle_abs (β := β) (h := h) (v := Λ*ζ) hK
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
  · have hw : (-11/50:ℝ) ≤ h-2*β-2*Λ*ζ ∧ h-2*β-2*Λ*ζ ≤ (933/500:ℝ) :=
      ⟨by linarith only [hw0], hw1⟩
    obtain ⟨hj0,hj1⟩ := mul_box hJ hw (by norm_num) (by norm_num)
    rw [abs_le]; norm_num [eta]
    constructor <;> linarith only [hj0,hj1]

lemma box_O_pos (β Λ K J ζ h : ℝ)
    (hb : (0:ℝ) ≤ β ∧ β ≤ (9/100:ℝ))
    (hL : 0 ≤ Λ ∧ Λ ≤ (3/5:ℝ)) (hK : (37/100:ℝ) ≤ K ∧ K ≤ (14/25:ℝ))
    (hJ : 0 ≤ J ∧ J ≤ (18/25:ℝ)) (hz : (-19/40:ℝ) ≤ ζ ∧ ζ ≤ (0:ℝ))
    (hh : (4/5:ℝ) ≤ h ∧ h ≤ 177/100) :
    |h-2*β-2*Λ*ζ| ≤ (117/50:ℝ) ∧
    |(82/37)*β-eta/2+Λ*ζ+K*(h-2*β-2*Λ*ζ)| ≤ (11/20:ℝ) ∧
    |-eta+J*(h-2*β-2*Λ*ζ)| ≤ (231/200:ℝ) := by
  obtain ⟨hv0,hv1⟩ := mul_box hL hz (by norm_num) (by norm_num)
  norm_num at hv0 hv1
  have hw0 : (31/50:ℝ) ≤ h-2*β-2*Λ*ζ := by linarith only [hb.2, hh.1, hv1]
  have hw1 : h-2*β-2*Λ*ζ ≤ (117/50:ℝ) := by linarith only [hb.1, hh.2, hv0]
  refine ⟨abs_le.mpr ⟨by linarith only [hw0], by linarith only [hw1]⟩, ?_, ?_⟩
  · simp only [mul_assoc]
    apply middle_abs (β := β) (h := h) (v := Λ*ζ) hK
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
  · have hw : (0:ℝ) ≤ h-2*β-2*Λ*ζ ∧ h-2*β-2*Λ*ζ ≤ (117/50:ℝ) :=
      ⟨by linarith only [hw0], hw1⟩
    obtain ⟨hj0,hj1⟩ := mul_box hJ hw (by norm_num) (by norm_num)
    rw [abs_le]; norm_num [eta]
    constructor <;> linarith only [hj0,hj1]

lemma box_P_neg (β Λ K J ζ h : ℝ)
    (hb : (83/1000:ℝ) ≤ β ∧ β ≤ (3/20:ℝ))
    (hL : 0 ≤ Λ ∧ Λ ≤ (101/100:ℝ)) (hK : (29/100:ℝ) ≤ K ∧ K ≤ (23/50:ℝ))
    (hJ : 0 ≤ J ∧ J ≤ (18/25:ℝ)) (hz : (-2/25:ℝ) ≤ ζ ∧ ζ ≤ (7/10:ℝ))
    (hh : (4/5:ℝ) ≤ h ∧ h ≤ 177/100) :
    |h-2*β-2*Λ*ζ| ≤ (883/500:ℝ) ∧
    |(82/37)*β-eta/2+Λ*ζ+K*(h-2*β-2*Λ*ζ)| ≤ (49/100:ℝ) ∧
    |-eta+J*(h-2*β-2*Λ*ζ)| ≤ (1813/1000:ℝ) := by
  obtain ⟨hv0,hv1⟩ := mul_box hL hz (by norm_num) (by norm_num)
  norm_num at hv0 hv1
  have hw0 : (-457/500:ℝ) ≤ h-2*β-2*Λ*ζ := by linarith only [hb.2, hh.1, hv1]
  have hw1 : h-2*β-2*Λ*ζ ≤ (2207/1250:ℝ) := by linarith only [hb.1, hh.2, hv0]
  refine ⟨abs_le.mpr ⟨by linarith only [hw0], by linarith only [hw1]⟩, ?_, ?_⟩
  · simp only [mul_assoc]
    apply middle_abs (β := β) (h := h) (v := Λ*ζ) hK
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
  · have hw : (-457/500:ℝ) ≤ h-2*β-2*Λ*ζ ∧ h-2*β-2*Λ*ζ ≤ (2207/1250:ℝ) :=
      ⟨by linarith only [hw0], hw1⟩
    obtain ⟨hj0,hj1⟩ := mul_box hJ hw (by norm_num) (by norm_num)
    rw [abs_le]; norm_num [eta]
    constructor <;> linarith only [hj0,hj1]

lemma box_P_pos (β Λ K J ζ h : ℝ)
    (hb : (83/1000:ℝ) ≤ β ∧ β ≤ (3/20:ℝ))
    (hL : 0 ≤ Λ ∧ Λ ≤ (101/100:ℝ)) (hK : (29/100:ℝ) ≤ K ∧ K ≤ (23/50:ℝ))
    (hJ : 0 ≤ J ∧ J ≤ (18/25:ℝ)) (hz : (-19/40:ℝ) ≤ ζ ∧ ζ ≤ (0:ℝ))
    (hh : (4/5:ℝ) ≤ h ∧ h ≤ 177/100) :
    |h-2*β-2*Λ*ζ| ≤ (641/250:ℝ) ∧
    |(82/37)*β-eta/2+Λ*ζ+K*(h-2*β-2*Λ*ζ)| ≤ (433/1000:ℝ) ∧
    |-eta+J*(h-2*β-2*Λ*ζ)| ≤ (231/200:ℝ) := by
  obtain ⟨hv0,hv1⟩ := mul_box hL hz (by norm_num) (by norm_num)
  norm_num at hv0 hv1
  have hw0 : (1/2:ℝ) ≤ h-2*β-2*Λ*ζ := by linarith only [hb.2, hh.1, hv1]
  have hw1 : h-2*β-2*Λ*ζ ≤ (5127/2000:ℝ) := by linarith only [hb.1, hh.2, hv0]
  refine ⟨abs_le.mpr ⟨by linarith only [hw0], by linarith only [hw1]⟩, ?_, ?_⟩
  · simp only [mul_assoc]
    apply middle_abs (β := β) (h := h) (v := Λ*ζ) hK
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
  · have hw : (0:ℝ) ≤ h-2*β-2*Λ*ζ ∧ h-2*β-2*Λ*ζ ≤ (5127/2000:ℝ) :=
      ⟨by linarith only [hw0], hw1⟩
    obtain ⟨hj0,hj1⟩ := mul_box hJ hw (by norm_num) (by norm_num)
    rw [abs_le]; norm_num [eta]
    constructor <;> linarith only [hj0,hj1]

lemma box_R_neg (β Λ K J ζ h : ℝ)
    (hb : (7/50:ℝ) ≤ β ∧ β ≤ (23/100:ℝ))
    (hL : 0 ≤ Λ ∧ Λ ≤ (119/100:ℝ)) (hK : (29/100:ℝ) ≤ K ∧ K ≤ (371/1000:ℝ))
    (hJ : 0 ≤ J ∧ J ≤ (17/25:ℝ)) (hz : (-2/25:ℝ) ≤ ζ ∧ ζ ≤ (7/10:ℝ))
    (hh : (4/5:ℝ) ≤ h ∧ h ≤ 177/100) :
    |h-2*β-2*Λ*ζ| ≤ (1681/1000:ℝ) ∧
    |(82/37)*β-eta/2+Λ*ζ+K*(h-2*β-2*Λ*ζ)| ≤ (83/125:ℝ) ∧
    |-eta+J*(h-2*β-2*Λ*ζ)| ≤ (2057/1000:ℝ) := by
  obtain ⟨hv0,hv1⟩ := mul_box hL hz (by norm_num) (by norm_num)
  norm_num at hv0 hv1
  have hw0 : (-663/500:ℝ) ≤ h-2*β-2*Λ*ζ := by linarith only [hb.2, hh.1, hv1]
  have hw1 : h-2*β-2*Λ*ζ ≤ (4201/2500:ℝ) := by linarith only [hb.1, hh.2, hv0]
  refine ⟨abs_le.mpr ⟨by linarith only [hw0], by linarith only [hw1]⟩, ?_, ?_⟩
  · simp only [mul_assoc]
    apply middle_abs (β := β) (h := h) (v := Λ*ζ) hK
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
  · have hw : (-663/500:ℝ) ≤ h-2*β-2*Λ*ζ ∧ h-2*β-2*Λ*ζ ≤ (4201/2500:ℝ) :=
      ⟨by linarith only [hw0], hw1⟩
    obtain ⟨hj0,hj1⟩ := mul_box hJ hw (by norm_num) (by norm_num)
    rw [abs_le]; norm_num [eta]
    constructor <;> linarith only [hj0,hj1]

lemma box_R_pos (β Λ K J ζ h : ℝ)
    (hb : (7/50:ℝ) ≤ β ∧ β ≤ (23/100:ℝ))
    (hL : 0 ≤ Λ ∧ Λ ≤ (119/100:ℝ)) (hK : (29/100:ℝ) ≤ K ∧ K ≤ (371/1000:ℝ))
    (hJ : 0 ≤ J ∧ J ≤ (17/25:ℝ)) (hz : (-19/40:ℝ) ≤ ζ ∧ ζ ≤ (0:ℝ))
    (hh : (4/5:ℝ) ≤ h ∧ h ≤ 177/100) :
    |h-2*β-2*Λ*ζ| ≤ (2621/1000:ℝ) ∧
    |(82/37)*β-eta/2+Λ*ζ+K*(h-2*β-2*Λ*ζ)| ≤ (21/50:ℝ) ∧
    |-eta+J*(h-2*β-2*Λ*ζ)| ≤ (231/200:ℝ) := by
  obtain ⟨hv0,hv1⟩ := mul_box hL hz (by norm_num) (by norm_num)
  norm_num at hv0 hv1
  have hw0 : (17/50:ℝ) ≤ h-2*β-2*Λ*ζ := by linarith only [hb.2, hh.1, hv1]
  have hw1 : h-2*β-2*Λ*ζ ≤ (5241/2000:ℝ) := by linarith only [hb.1, hh.2, hv0]
  refine ⟨abs_le.mpr ⟨by linarith only [hw0], by linarith only [hw1]⟩, ?_, ?_⟩
  · simp only [mul_assoc]
    apply middle_abs (β := β) (h := h) (v := Λ*ζ) hK
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
  · have hw : (0:ℝ) ≤ h-2*β-2*Λ*ζ ∧ h-2*β-2*Λ*ζ ≤ (5241/2000:ℝ) :=
      ⟨by linarith only [hw0], hw1⟩
    obtain ⟨hj0,hj1⟩ := mul_box hJ hw (by norm_num) (by norm_num)
    rw [abs_le]; norm_num [eta]
    constructor <;> linarith only [hj0,hj1]

lemma box_U_neg (β Λ K J ζ h : ℝ)
    (hb : (11/50:ℝ) ≤ β ∧ β ≤ (171/500:ℝ))
    (hL : 0 ≤ Λ ∧ Λ ≤ (119/100:ℝ)) (hK : (29/100:ℝ) ≤ K ∧ K ≤ (199/500:ℝ))
    (hJ : 0 ≤ J ∧ J ≤ (61/100:ℝ)) (hz : (-2/25:ℝ) ≤ ζ ∧ ζ ≤ (7/10:ℝ))
    (hh : (4/5:ℝ) ≤ h ∧ h ≤ 177/100) :
    |h-2*β-2*Λ*ζ| ≤ (31/20:ℝ) ∧
    |(82/37)*β-eta/2+Λ*ζ+K*(h-2*β-2*Λ*ζ)| ≤ (847/1000:ℝ) ∧
    |-eta+J*(h-2*β-2*Λ*ζ)| ≤ (2101/1000:ℝ) := by
  obtain ⟨hv0,hv1⟩ := mul_box hL hz (by norm_num) (by norm_num)
  norm_num at hv0 hv1
  have hw0 : (-31/20:ℝ) ≤ h-2*β-2*Λ*ζ := by linarith only [hb.2, hh.1, hv1]
  have hw1 : h-2*β-2*Λ*ζ ≤ (3801/2500:ℝ) := by linarith only [hb.1, hh.2, hv0]
  refine ⟨abs_le.mpr ⟨by linarith only [hw0], by linarith only [hw1]⟩, ?_, ?_⟩
  · simp only [mul_assoc]
    apply middle_abs (β := β) (h := h) (v := Λ*ζ) hK
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
  · have hw : (-31/20:ℝ) ≤ h-2*β-2*Λ*ζ ∧ h-2*β-2*Λ*ζ ≤ (3801/2500:ℝ) :=
      ⟨by linarith only [hw0], hw1⟩
    obtain ⟨hj0,hj1⟩ := mul_box hJ hw (by norm_num) (by norm_num)
    rw [abs_le]; norm_num [eta]
    constructor <;> linarith only [hj0,hj1]

lemma box_U_pos (β Λ K J ζ h : ℝ)
    (hb : (11/50:ℝ) ≤ β ∧ β ≤ (171/500:ℝ))
    (hL : 0 ≤ Λ ∧ Λ ≤ (119/100:ℝ)) (hK : (29/100:ℝ) ≤ K ∧ K ≤ (199/500:ℝ))
    (hJ : 0 ≤ J ∧ J ≤ (61/100:ℝ)) (hz : (-19/40:ℝ) ≤ ζ ∧ ζ ≤ (0:ℝ))
    (hh : (4/5:ℝ) ≤ h ∧ h ≤ 177/100) :
    |h-2*β-2*Λ*ζ| ≤ (2461/1000:ℝ) ∧
    |(82/37)*β-eta/2+Λ*ζ+K*(h-2*β-2*Λ*ζ)| ≤ (123/200:ℝ) ∧
    |-eta+J*(h-2*β-2*Λ*ζ)| ≤ (231/200:ℝ) := by
  obtain ⟨hv0,hv1⟩ := mul_box hL hz (by norm_num) (by norm_num)
  norm_num at hv0 hv1
  have hw0 : (29/250:ℝ) ≤ h-2*β-2*Λ*ζ := by linarith only [hb.2, hh.1, hv1]
  have hw1 : h-2*β-2*Λ*ζ ≤ (4921/2000:ℝ) := by linarith only [hb.1, hh.2, hv0]
  refine ⟨abs_le.mpr ⟨by linarith only [hw0], by linarith only [hw1]⟩, ?_, ?_⟩
  · simp only [mul_assoc]
    apply middle_abs (β := β) (h := h) (v := Λ*ζ) hK
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
  · have hw : (0:ℝ) ≤ h-2*β-2*Λ*ζ ∧ h-2*β-2*Λ*ζ ≤ (4921/2000:ℝ) :=
      ⟨by linarith only [hw0], hw1⟩
    obtain ⟨hj0,hj1⟩ := mul_box hJ hw (by norm_num) (by norm_num)
    rw [abs_le]; norm_num [eta]
    constructor <;> linarith only [hj0,hj1]

lemma box_V_neg (β Λ K J ζ h : ℝ)
    (hb : (337/1000:ℝ) ≤ β ∧ β ≤ (9/20:ℝ))
    (hL : 0 ≤ Λ ∧ Λ ≤ (83/100:ℝ)) (hK : (31/100:ℝ) ≤ K ∧ K ≤ (2/5:ℝ))
    (hJ : 0 ≤ J ∧ J ≤ (1/2:ℝ)) (hz : (-2/25:ℝ) ≤ ζ ∧ ζ ≤ (7/10:ℝ))
    (hh : (4/5:ℝ) ≤ h ∧ h ≤ 177/100) :
    |h-2*β-2*Λ*ζ| ≤ (1263/1000:ℝ) ∧
    |(82/37)*β-eta/2+Λ*ζ+K*(h-2*β-2*Λ*ζ)| ≤ (114/125:ℝ) ∧
    |-eta+J*(h-2*β-2*Λ*ζ)| ≤ (1787/1000:ℝ) := by
  obtain ⟨hv0,hv1⟩ := mul_box hL hz (by norm_num) (by norm_num)
  norm_num at hv0 hv1
  have hw0 : (-631/500:ℝ) ≤ h-2*β-2*Λ*ζ := by linarith only [hb.2, hh.1, hv1]
  have hw1 : h-2*β-2*Λ*ζ ≤ (768/625:ℝ) := by linarith only [hb.1, hh.2, hv0]
  refine ⟨abs_le.mpr ⟨by linarith only [hw0], by linarith only [hw1]⟩, ?_, ?_⟩
  · simp only [mul_assoc]
    apply middle_abs (β := β) (h := h) (v := Λ*ζ) hK
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
  · have hw : (-631/500:ℝ) ≤ h-2*β-2*Λ*ζ ∧ h-2*β-2*Λ*ζ ≤ (768/625:ℝ) :=
      ⟨by linarith only [hw0], hw1⟩
    obtain ⟨hj0,hj1⟩ := mul_box hJ hw (by norm_num) (by norm_num)
    rw [abs_le]; norm_num [eta]
    constructor <;> linarith only [hj0,hj1]

lemma box_V_pos (β Λ K J ζ h : ℝ)
    (hb : (337/1000:ℝ) ≤ β ∧ β ≤ (9/20:ℝ))
    (hL : 0 ≤ Λ ∧ Λ ≤ (83/100:ℝ)) (hK : (31/100:ℝ) ≤ K ∧ K ≤ (2/5:ℝ))
    (hJ : 0 ≤ J ∧ J ≤ (1/2:ℝ)) (hz : (-19/40:ℝ) ≤ ζ ∧ ζ ≤ (0:ℝ))
    (hh : (4/5:ℝ) ≤ h ∧ h ≤ 177/100) :
    |h-2*β-2*Λ*ζ| ≤ (377/200:ℝ) ∧
    |(82/37)*β-eta/2+Λ*ζ+K*(h-2*β-2*Λ*ζ)| ≤ (77/100:ℝ) ∧
    |-eta+J*(h-2*β-2*Λ*ζ)| ≤ (241/200:ℝ) := by
  obtain ⟨hv0,hv1⟩ := mul_box hL hz (by norm_num) (by norm_num)
  norm_num at hv0 hv1
  have hw0 : (-1/10:ℝ) ≤ h-2*β-2*Λ*ζ := by linarith only [hb.2, hh.1, hv1]
  have hw1 : h-2*β-2*Λ*ζ ≤ (3769/2000:ℝ) := by linarith only [hb.1, hh.2, hv0]
  refine ⟨abs_le.mpr ⟨by linarith only [hw0], by linarith only [hw1]⟩, ?_, ?_⟩
  · simp only [mul_assoc]
    apply middle_abs (β := β) (h := h) (v := Λ*ζ) hK
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
  · have hw : (-1/10:ℝ) ≤ h-2*β-2*Λ*ζ ∧ h-2*β-2*Λ*ζ ≤ (3769/2000:ℝ) :=
      ⟨by linarith only [hw0], hw1⟩
    obtain ⟨hj0,hj1⟩ := mul_box hJ hw (by norm_num) (by norm_num)
    rw [abs_le]; norm_num [eta]
    constructor <;> linarith only [hj0,hj1]

lemma box_T_neg (β Λ K J ζ h : ℝ)
    (hb : (89/200:ℝ) ≤ β ∧ β ≤ (1/2:ℝ))
    (hL : 0 ≤ Λ ∧ Λ ≤ (1/5:ℝ)) (hK : (8/25:ℝ) ≤ K ∧ K ≤ (2/5:ℝ))
    (hJ : 0 ≤ J ∧ J ≤ (12/25:ℝ)) (hz : (-2/25:ℝ) ≤ ζ ∧ ζ ≤ (7/10:ℝ))
    (hh : (4/5:ℝ) ≤ h ∧ h ≤ 177/100) :
    |h-2*β-2*Λ*ζ| ≤ (913/1000:ℝ) ∧
    |(82/37)*β-eta/2+Λ*ζ+K*(h-2*β-2*Λ*ζ)| ≤ (869/1000:ℝ) ∧
    |-eta+J*(h-2*β-2*Λ*ζ)| ≤ (693/500:ℝ) := by
  obtain ⟨hv0,hv1⟩ := mul_box hL hz (by norm_num) (by norm_num)
  norm_num at hv0 hv1
  have hw0 : (-12/25:ℝ) ≤ h-2*β-2*Λ*ζ := by linarith only [hb.2, hh.1, hv1]
  have hw1 : h-2*β-2*Λ*ζ ≤ (114/125:ℝ) := by linarith only [hb.1, hh.2, hv0]
  refine ⟨abs_le.mpr ⟨by linarith only [hw0], by linarith only [hw1]⟩, ?_, ?_⟩
  · simp only [mul_assoc]
    apply middle_abs (β := β) (h := h) (v := Λ*ζ) hK
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
  · have hw : (-12/25:ℝ) ≤ h-2*β-2*Λ*ζ ∧ h-2*β-2*Λ*ζ ≤ (114/125:ℝ) :=
      ⟨by linarith only [hw0], hw1⟩
    obtain ⟨hj0,hj1⟩ := mul_box hJ hw (by norm_num) (by norm_num)
    rw [abs_le]; norm_num [eta]
    constructor <;> linarith only [hj0,hj1]

lemma box_T_pos (β Λ K J ζ h : ℝ)
    (hb : (89/200:ℝ) ≤ β ∧ β ≤ (1/2:ℝ))
    (hL : 0 ≤ Λ ∧ Λ ≤ (1/5:ℝ)) (hK : (8/25:ℝ) ≤ K ∧ K ≤ (2/5:ℝ))
    (hJ : 0 ≤ J ∧ J ≤ (12/25:ℝ)) (hz : (-19/40:ℝ) ≤ ζ ∧ ζ ≤ (0:ℝ))
    (hh : (4/5:ℝ) ≤ h ∧ h ≤ 177/100) :
    |h-2*β-2*Λ*ζ| ≤ (1071/1000:ℝ) ∧
    |(82/37)*β-eta/2+Λ*ζ+K*(h-2*β-2*Λ*ζ)| ≤ (21/25:ℝ) ∧
    |-eta+J*(h-2*β-2*Λ*ζ)| ≤ (1251/1000:ℝ) := by
  obtain ⟨hv0,hv1⟩ := mul_box hL hz (by norm_num) (by norm_num)
  norm_num at hv0 hv1
  have hw0 : (-1/5:ℝ) ≤ h-2*β-2*Λ*ζ := by linarith only [hb.2, hh.1, hv1]
  have hw1 : h-2*β-2*Λ*ζ ≤ (107/100:ℝ) := by linarith only [hb.1, hh.2, hv0]
  refine ⟨abs_le.mpr ⟨by linarith only [hw0], by linarith only [hw1]⟩, ?_, ?_⟩
  · simp only [mul_assoc]
    apply middle_abs (β := β) (h := h) (v := Λ*ζ) hK
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
    · rw [abs_le]; norm_num [eta]
      constructor <;> linarith only [hb.1, hb.2, hh.1, hh.2, hv0, hv1]
  · have hw : (-1/5:ℝ) ≤ h-2*β-2*Λ*ζ ∧ h-2*β-2*Λ*ζ ≤ (107/100:ℝ) :=
      ⟨by linarith only [hw0], hw1⟩
    obtain ⟨hj0,hj1⟩ := mul_box hJ hw (by norm_num) (by norm_num)
    rw [abs_le]; norm_num [eta]
    constructor <;> linarith only [hj0,hj1]

end Submission.Obl.Entropy__two_eigenvalue_secant_deduction
