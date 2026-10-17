import Mathlib

/-!
An elementary rational minorant for the logarithm. The derivative identity
is checked algebraically, so the estimates use exact rational arithmetic.
-/

namespace Submission.Obl.Entropy__absorption_logarithmic_cutoff

open Set

noncomputable def rationalLog (x : ℝ) : ℝ :=
  (x - 1) * (3*x^4 + 68*x^3 + 98*x^2 + 68*x + 3) /
    (30*x*(x+1)^3)

lemma hasDerivAt_log_sub_rationalLog {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => Real.log x - rationalLog x)
      (-(x-1)^6 / (10*x^2*(x+1)^4)) x := by
  have h₁ := hasDerivAt_id x
  have hN := (h₁.sub_const 1).mul
    (((((h₁.pow 4).const_mul 3).add ((h₁.pow 3).const_mul 68)).add
      ((h₁.pow 2).const_mul 98)).add (h₁.const_mul 68) |>.add_const 3)
  have hD := (h₁.const_mul 30).mul ((h₁.add_const 1).pow 3)
  convert! (Real.hasDerivAt_log hx.ne').sub (hN.div hD (by dsimp; positivity)) using 1
  dsimp
  field_simp
  ring

lemma rationalLog_le_log {x : ℝ} (hx : 0 < x) (hx₁ : x ≤ 1) :
    rationalLog x ≤ Real.log x := by
  have hm : AntitoneOn (fun x => Real.log x - rationalLog x) (Ioi 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
      (fun y hy => (hasDerivAt_log_sub_rationalLog hy).continuousAt.continuousWithinAt)
      (fun y hy => (hasDerivAt_log_sub_rationalLog (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    have hy₀ : 0 < y := interior_subset hy
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)
  have h := hm hx (by norm_num : (1:ℝ) ∈ Ioi 0) hx₁
  simpa [rationalLog] using h

lemma two_mul_sub_div_add_le_log {x : ℝ} (hx : 1 ≤ x) :
    2*(x-1)/(x+1) ≤ Real.log x := by
  have hd (y : ℝ) (hy : 0 < y) :
      HasDerivAt (fun y => Real.log y - 2*(y-1)/(y+1))
        ((y-1)^2 / (y*(y+1)^2)) y := by
    convert! (Real.hasDerivAt_log hy.ne').sub
      ((((hasDerivAt_id y).sub_const 1).const_mul 2).div
        ((hasDerivAt_id y).add_const 1) (by positivity)) using 1
    dsimp
    field_simp
    ring
  have hm : MonotoneOn (fun y => Real.log y - 2*(y-1)/(y+1)) (Ici 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
      (fun y hy => (hd y (by simpa using (lt_of_lt_of_le zero_lt_one hy))).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (lt_of_lt_of_le zero_lt_one (interior_subset hy))).hasDerivWithinAt) ?_
    intro y hy
    have hy₀ : 0 < y := lt_of_lt_of_le zero_lt_one (interior_subset hy)
    positivity
  have h := hm (by simp) hx hx
  norm_num at h
  linarith

end Submission.Obl.Entropy__absorption_logarithmic_cutoff
