import Mathlib
import ChallengeDeps
import Submission.Obl.Entropy__absorption_logarithmic_cutoff.LogBounds
set_option linter.unusedVariables false

/-!
The logarithmic cost of the affine inverse is bounded by the exact rigidity
weight. Two rationally certified scalar bounds give the constant and inverse
square-root branches of the cutoff.
-/

theorem Submission.Entropy.absorption_logarithmic_cutoff : ∀ z : ℝ, 0 ≤ z → 40 / (37 + 3*z) - 1 - Real.log (40 / (37 + 3*z)) ≤ (86/125) * ((3 * (z - 1)^2 / (37 + 3*z)) * ((3 : ℝ)/20 + ((49 : ℝ)/100)*(37/(37+3*z))) * (if z = 0 then (13 : ℝ)/100 else min ((13 : ℝ)/100) (32/(25*Real.sqrt z)))) := by
  intro z hz
  let s : ℝ := 40 / (37+3*z)
  let w : ℝ := (3*(z-1)^2/(37+3*z)) * (3/20 + (49/100)*(37/(37+3*z)))
  change s - 1 - Real.log s ≤ (86/125)*(w*
    (if z = 0 then 13/100 else min (13/100) (32/(25*Real.sqrt z))))
  rw [← mul_assoc]
  have hd : 0 < 37+3*z := by positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hsw : s*w = (2+(1813/300)*s)*(s-1)^2 := by
    dsimp [s, w]
    field_simp
    ring
  have hconstant : s-1-Real.log s ≤ (89/1000)*w := by
    apply (mul_le_mul_iff_left₀ hs).mp
    calc
      (s-1-Real.log s)*s = s*(s-1-Real.log s) := by ring
      _ ≤ (4/25+(13/25)*s)*(s-1)^2 :=
        Submission.Obl.Entropy__absorption_logarithmic_cutoff.log_cost_affine hs
      _ ≤ ((89/1000)*(2+(1813/300)*s))*(s-1)^2 := by
        gcongr
        linarith
      _ = ((89/1000)*w)*s := by nlinarith only [hsw]
  have hsqrt : (s-1-Real.log s)*Real.sqrt z ≤ (22/25)*w := by
    have hsz : s*z ≤ 40/3 := by
      have hprod : s*(37+3*z) = 40 := by dsimp [s]; field_simp
      nlinarith
    have ht : Real.sqrt s*Real.sqrt z ≤ 11/3 := by
      have hsq : (Real.sqrt s*Real.sqrt z)^2 = s*z := by
        rw [mul_pow, Real.sq_sqrt hs.le, Real.sq_sqrt hz]
      nlinarith
    have hcoeff : (Real.sqrt s*Real.sqrt z)*(239/500+(7/5)*s) ≤
        (22/25)*(2+(1813/300)*s) := by
      calc
        _ ≤ (11/3)*(239/500+(7/5)*s) := by gcongr
        _ ≤ _ := by linarith
    have hlog := mul_le_mul_of_nonneg_right
      (Submission.Obl.Entropy__absorption_logarithmic_cutoff.log_cost_sqrt hs)
      (Real.sqrt_nonneg z)
    apply (mul_le_mul_iff_left₀ hs).mp
    calc
      ((s-1-Real.log s)*Real.sqrt z)*s =
          (s*(s-1-Real.log s))*Real.sqrt z := by ring
      _ ≤ (Real.sqrt s*(239/500+(7/5)*s)*(s-1)^2)*Real.sqrt z := hlog
      _ = ((Real.sqrt s*Real.sqrt z)*(239/500+(7/5)*s))*(s-1)^2 := by ring
      _ ≤ ((22/25)*(2+(1813/300)*s))*(s-1)^2 :=
        mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
      _ = ((22/25)*w)*s := by nlinarith only [hsw]
  have hc : s-1-Real.log s ≤ (86/125)*w*(13/100) := by
    calc
      _ ≤ (89/1000)*w := hconstant
      _ ≤ _ := by nlinarith only [hw]
  by_cases hz₀ : z = 0
  · simpa only [if_pos hz₀] using hc
  · rw [if_neg hz₀, mul_min_of_nonneg _ _ (by positivity : 0 ≤ (86/125)*w)]
    apply le_min hc
    have ht : 0 < Real.sqrt z := Real.sqrt_pos.mpr (lt_of_le_of_ne hz (Ne.symm hz₀))
    have hbound : (s-1-Real.log s)*Real.sqrt z ≤ (86/125)*w*(32/25) := by
      calc
        _ ≤ (22/25)*w := hsqrt
        _ ≤ _ := by nlinarith only [hw]
    calc
      _ ≤ ((86/125)*w*(32/25))/Real.sqrt z := (le_div_iff₀ ht).mpr hbound
      _ = _ := by ring
