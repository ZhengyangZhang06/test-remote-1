import Submission.Obl.Entropy__two_eigenvalue_secant_deduction.TailCost
import Submission.Obl.Entropy__two_eigenvalue_secant_deduction.Secant

open Set

namespace Submission.Obl.Entropy__two_eigenvalue_secant_deduction

noncomputable def blend (A B len d : ℝ) := B-(B-A)*len/d

lemma blend_between {A B len d : ℝ} (hAB : A ≤ B) (hl : 0 ≤ len) (hd : 0 < d)
    (hld : len ≤ d) : A ≤ blend A B len d ∧ blend A B len d ≤ B := by
  have hf : 0 ≤ len/d := div_nonneg hl hd.le
  have hf1 : len/d ≤ 1 := (div_le_one hd).mpr hld
  have hb := mul_nonneg (sub_nonneg.mpr hAB) hf
  have ha := mul_nonneg (sub_nonneg.mpr hAB) (sub_nonneg.mpr hf1)
  unfold blend
  rw [div_eq_mul_inv] at *
  constructor <;> nlinarith only [hb,ha]

lemma partial_norm_bound {j a c cut A B len : ℝ} (hac : a < c)
    (hcut : cut ∈ Icc a c) (hAB : A ≤ B) (hlen : 0 ≤ len)
    (hlen' : len ≤ logq cut-logq a)
    (hlo : ∀ x ∈ Icc a cut, ‖J j x-J j a‖ ≤ A*(logq x-logq a))
    (hhi : ∀ x ∈ Icc cut c, ‖J j x-J j cut‖ ≤ B*(logq x-logq cut)) :
    ∀ x ∈ Icc a c, ‖J j x-J j a‖ ≤ blend A B len (delta c a)*(logq x-logq a) := by
  have hδ : 0 < delta c a := sub_pos.mpr (strictMono_logq hac)
  have hlenδ : len ≤ delta c a := by
    dsimp only [delta]
    linarith [strictMono_logq.monotone hcut.2]
  obtain ⟨hA,hB⟩ := blend_between hAB hlen hδ hlenδ
  have he : (B-blend A B len (delta c a))*delta c a = (B-A)*len := by
    unfold blend
    field_simp
    <;> ring
  intro x hx
  have hs0 : 0 ≤ logq x-logq a := sub_nonneg.mpr (strictMono_logq.monotone hx.1)
  have hsδ : logq x-logq a ≤ delta c a := by
    dsimp only [delta]; linarith [strictMono_logq.monotone hx.2]
  by_cases hxc : x ≤ cut
  · exact (hlo x ⟨hx.1,hxc⟩).trans (mul_le_mul_of_nonneg_right hA hs0)
  · have h1 := hlo cut ⟨hcut.1,le_rfl⟩
    have h2 := hhi x ⟨(lt_of_not_ge hxc).le,hx.2⟩
    have htri : ‖J j x-J j a‖ ≤ ‖J j x-J j cut‖+‖J j cut-J j a‖ :=
      calc
        _ = ‖(J j x-J j cut)+(J j cut-J j a)‖ := by congr 1; module
        _ ≤ _ := norm_add_le _ _
    have ha := mul_nonneg (sub_nonneg.mpr hAB) (sub_nonneg.mpr hlen')
    have hb := mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr hsδ)
    nlinarith only [h1,h2,htri,ha,hb,he]

lemma sqrt_blend_le {A B len d : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hl : 0 ≤ len)
    (hd : 0 < d) (hld : len ≤ d) :
    blend (Real.sqrt A) (Real.sqrt B) len d ≤ Real.sqrt (blend A B len d) := by
  let r := len/d
  have hr0 : 0 ≤ r := div_nonneg hl hd.le
  have hr1 : r ≤ 1 := (div_le_one hd).mpr hld
  have hid (u v : ℝ) : blend u v len d = (1-r)*v+r*u := by
    dsimp only [blend,r]; ring
  rw [hid, hid]
  have hp : 0 ≤ (1-r)*B+r*A := by positivity
  have hc : 0 ≤ (1-r)*Real.sqrt B+r*Real.sqrt A := by positivity
  apply (Real.le_sqrt hc hp).2
  calc
    _ ≤ (1-r)*(Real.sqrt B)^2+r*(Real.sqrt A)^2 := by
      have h := mul_nonneg (mul_nonneg hr0 (sub_nonneg.mpr hr1))
        (sq_nonneg (Real.sqrt A-Real.sqrt B))
      nlinarith only [h]
    _ = _ := by rw [Real.sq_sqrt hA, Real.sq_sqrt hB]

lemma partial_two_costs {j a c cut A B len : ℝ} (hac : a < c)
    (hcut : cut ∈ Icc a c) (hA : 0 ≤ A) (hAB : A ≤ B) (hlen : 0 ≤ len)
    (hlen' : len ≤ logq cut-logq a) (hcj : Certificate j)
    (hC : ∀ x, Certificate x)
    (hlo : ∀ x ∈ Ioo a cut, Fcost j x ≤ A)
    (hhi : ∀ x ∈ Ioo cut c, Fcost j x ≤ B) :
    ∀ x ∈ Icc a c, ‖J j x-J j a‖ ≤
      Real.sqrt (blend A B len (delta c a))*(logq x-logq a) := by
  have hδ : 0 < delta c a := sub_pos.mpr (strictMono_logq hac)
  have hlenδ : len ≤ delta c a := by
    dsimp only [delta]; linarith [strictMono_logq.monotone hcut.2]
  have h := partial_norm_bound hac hcut (Real.sqrt_le_sqrt hAB) hlen hlen'
    (fun x hx => J_sub_le_open hx.1 hA hcj.1
      (fun y _ => (hC y).2.2.2.1) (fun y hy => hlo y ⟨hy.1,hy.2.trans_le hx.2⟩))
    (fun x hx => J_sub_le_open hx.1 (hA.trans hAB) hcj.1
      (fun y _ => (hC y).2.2.2.1) (fun y hy => hhi y ⟨hy.1,hy.2.trans_le hx.2⟩))
  intro x hx
  exact (h x hx).trans (mul_le_mul_of_nonneg_right
    (sqrt_blend_le hA (hA.trans hAB) hlen hδ hlenδ)
    (sub_nonneg.mpr (strictMono_logq.monotone hx.1)))

end Submission.Obl.Entropy__two_eigenvalue_secant_deduction
