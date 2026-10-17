import Mathlib

open Set

namespace Submission.Obl.Entropy__hazard_secant_surplus

lemma nonneg_of_derivative_nonneg {f f' : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (f' x) x)
    (h0 : 0 ≤ f 0) (hn : ∀ x, 0 ≤ x → 0 ≤ f' x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
    · exact fun y _ => (hd y).continuousAt.continuousWithinAt
    · exact fun y _ => (hd y).hasDerivWithinAt
    · intro y hy
      exact hn y (show y ∈ Ici 0 from interior_subset hy)
  exact h0.trans (hm self_mem_Ici hx hx)

lemma sinh_support {x : ℝ} (hx : 0 ≤ x) : 0 ≤ x * Real.cosh x - Real.sinh x := by
  have hd (x : ℝ) : HasDerivAt (fun x => x * Real.cosh x - Real.sinh x) (x * Real.sinh x) x := by
    convert! ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub (Real.hasDerivAt_sinh x) using 1
    simp only [id_eq]
    ring
  exact nonneg_of_derivative_nonneg hd (by simp)
    (fun y hy => mul_nonneg hy (Real.sinh_nonneg_iff.mpr hy)) hx

lemma hyperbolic_comparison_base {x : ℝ} (hx : 0 ≤ x) :
    2 * Real.sinh x ^ 2 ≤ x * Real.sinh x * Real.cosh x + x ^ 2 := by
  let F : ℝ → ℝ := fun x => x * Real.sinh x * Real.cosh x + x ^ 2 - 2 * Real.sinh x ^ 2
  let F' : ℝ → ℝ := fun x => x * (Real.cosh x ^ 2 + Real.sinh x ^ 2) + 2 * x -
    3 * Real.sinh x * Real.cosh x
  have hd (x : ℝ) : HasDerivAt F (F' x) x := by
    convert! ((((hasDerivAt_id x).mul (Real.hasDerivAt_sinh x)).mul (Real.hasDerivAt_cosh x)).add
      ((hasDerivAt_id x).pow 2)).sub (((Real.hasDerivAt_sinh x).pow 2).const_mul 2) using 1
    dsimp only [F', id_eq, Pi.mul_apply]
    ring
  have hd' (x : ℝ) : HasDerivAt F'
      (4 * Real.sinh x * (x * Real.cosh x - Real.sinh x)) x := by
    convert! (((hasDerivAt_id x).mul (((Real.hasDerivAt_cosh x).pow 2).add
      ((Real.hasDerivAt_sinh x).pow 2))).add ((hasDerivAt_id x).const_mul 2)).sub
      (((Real.hasDerivAt_sinh x).const_mul 3).mul (Real.hasDerivAt_cosh x)) using 1
    dsimp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.pow_apply]
    norm_num only [Nat.reduceSub, Nat.cast_ofNat, pow_one]
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  have hf' (x : ℝ) (hx : 0 ≤ x) : 0 ≤ F' x :=
    nonneg_of_derivative_nonneg hd' (by simp [F'])
      (fun y hy => mul_nonneg (mul_nonneg (by norm_num) (Real.sinh_nonneg_iff.mpr hy))
        (sinh_support hy)) hx
  have hf := nonneg_of_derivative_nonneg hd (by simp [F]) hf' hx
  dsimp only [F] at hf
  linarith

noncomputable def cothCorrection (x : ℝ) : ℝ := x * Real.cosh x / Real.sinh x - 1

lemma correction_ge (x : ℝ) (hx : 0 < x) :
    1 - (x / Real.sinh x) ^ 2 ≤ cothCorrection x := by
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have h := hyperbolic_comparison_base hx.le
  unfold cothCorrection
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hs)).mp
  field_simp [ne_of_gt hs]
  nlinarith

lemma hasDerivAt_scaledCorrection (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y => cothCorrection y / y ^ 2)
      ((2 * Real.sinh x ^ 2 - x * Real.sinh x * Real.cosh x - x ^ 2) /
        (x ^ 3 * Real.sinh x ^ 2)) x := by
  have hs : Real.sinh x ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hx)
  convert! (((((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).div (Real.hasDerivAt_sinh x) hs).sub_const 1).div
    ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 (ne_of_gt hx))) using 1
  dsimp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, id_eq]
  field_simp [hs, ne_of_gt hx]
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, pow_one]
  nlinarith [congrArg (fun t : ℝ => x ^ 3 * t) (Real.cosh_sq_sub_sinh_sq x)]

lemma antitoneOn_scaledCorrection : AntitoneOn (fun x => cothCorrection x / x ^ 2) (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi _)
  · exact fun x hx => (hasDerivAt_scaledCorrection x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_scaledCorrection x (by simpa only [interior_Ioi, mem_Ioi] using hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa only [interior_Ioi, mem_Ioi] using hx
    rw [(hasDerivAt_scaledCorrection x hx').deriv]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hyperbolic_comparison_base hx'.le]) (by positivity)

noncomputable def sinhc (x : ℝ) : ℝ := if x = 0 then 1 else Real.sinh x / x

lemma sinhc_pos {x : ℝ} (hx : 0 ≤ x) : 0 < sinhc x := by
  unfold sinhc
  split_ifs with h
  · norm_num
  · exact div_pos (Real.sinh_pos_iff.mpr (lt_of_le_of_ne hx (Ne.symm h)))
      (lt_of_le_of_ne hx (Ne.symm h))

lemma sinhc_comparison {x m : ℝ} (hx : 0 < x) (hm : 0 ≤ m) (hm1 : m ≤ 1) :
    1 + m * (1 - (x / Real.sinh x) ^ 2) ≤ sinhc ((1 + m) * x) / (sinhc x * sinhc (m * x)) := by
  by_cases hm0 : m = 0
  · subst m
    simp [sinhc, ne_of_gt hx, ne_of_gt (Real.sinh_pos_iff.mpr hx)]
  have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
  have hmx : 0 < m * x := mul_pos hmpos hx
  have hs := antitoneOn_scaledCorrection hmx hx (mul_le_of_le_one_left hx.le hm1)
  have hA : m ^ 2 * cothCorrection x ≤ cothCorrection (m * x) := by
    have h := (div_le_div_iff₀ (sq_pos_of_pos hx) (sq_pos_of_pos hmx)).mp hs
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hx)).mp
    convert h using 1 <;> ring
  have hr : sinhc ((1 + m) * x) / (sinhc x * sinhc (m * x)) =
      1 + (m * cothCorrection x + cothCorrection (m * x)) / (1 + m) := by
    have hsum : (1 + m) * x = x + m * x := by ring
    have hsumpos : 0 < (1 + m) * x := mul_pos (by linarith) hx
    simp only [sinhc, if_neg (ne_of_gt hx), if_neg (ne_of_gt hmx), if_neg (ne_of_gt hsumpos),
      cothCorrection]
    rw [hsum, Real.sinh_add]
    field_simp [ne_of_gt hx, hm0, ne_of_gt (Real.sinh_pos_iff.mpr hx),
      ne_of_gt (Real.sinh_pos_iff.mpr hmx), ne_of_gt (show 0 < 1 + m by linarith)]
    ring
  rw [hr]
  have hg := mul_le_mul_of_nonneg_left (correction_ge x hx) hm
  apply add_le_add_right ?_ 1
  apply (le_div_iff₀ (show 0 < 1 + m by linarith)).mpr
  nlinarith [mul_nonneg (show 0 ≤ 1 + m by linarith) (sub_nonneg.mpr hg)]

lemma sinh_taylor_lower {x : ℝ} (hx : 0 ≤ x) :
    x + x ^ 3 / 6 + x ^ 5 / 120 + x ^ 7 / 5040 ≤ Real.sinh x := by
  have h := (Real.hasSum_sinh x).summable.sum_le_tsum (Finset.range 4)
    (fun n _ => div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _))
  rw [(Real.hasSum_sinh x).tsum_eq] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  exact h

lemma sinhc_taylor_lower {x : ℝ} (hx : 0 < x) :
    1 + x ^ 2 / 3 + 2 * x ^ 4 / 45 + x ^ 6 / 315 ≤ sinhc x ^ 2 := by
  have h := sinh_taylor_lower hx.le
  have hp : 0 ≤ x + x ^ 3 / 6 + x ^ 5 / 120 + x ^ 7 / 5040 := by positivity
  have hh := sq_le_sq₀ hp (Real.sinh_nonneg_iff.mpr hx.le) |>.mpr h
  have hrem : 0 ≤ 41 * x ^ 10 / 302400 + x ^ 12 / 302400 + x ^ 14 / 25401600 := by positivity
  have hpoly : (1 + x ^ 2 / 3 + 2 * x ^ 4 / 45 + x ^ 6 / 315) * x ^ 2 ≤ Real.sinh x ^ 2 := by
    nlinarith
  simp only [sinhc, if_neg (ne_of_gt hx), div_pow]
  exact (le_div_iff₀ (sq_pos_of_pos hx)).mpr hpoly

lemma sinhc_surplus {x m : ℝ} (hx : 0 < x) (hm : 0 ≤ m) :
    (1 + m) / 16 * (1 + (2 * x) ^ 2 / 30 + (2 * x) ^ 4 / 1680) * (2 * x) ^ 2 ≤
      (3 / 4 : ℝ) * (1 + m) * (sinhc x ^ 2 - 1) := by
  have h := mul_le_mul_of_nonneg_left (sinhc_taylor_lower hx)
    (show 0 ≤ (3 / 4 : ℝ) * (1 + m) by positivity)
  nlinarith

end Submission.Obl.Entropy__hazard_secant_surplus
