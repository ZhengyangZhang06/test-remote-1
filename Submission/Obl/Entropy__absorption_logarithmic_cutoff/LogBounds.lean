import Submission.Obl.Entropy__absorption_logarithmic_cutoff.RationalLog

namespace Submission.Obl.Entropy__absorption_logarithmic_cutoff

/-- An affine majorant for the normalized logarithmic cost, including its zero at one. -/
lemma log_cost_affine {s : ℝ} (hs : 0 < s) :
    s * (s - 1 - Real.log s) ≤ (4/25 + (13/25)*s) * (s-1)^2 := by
  by_cases hs₁ : s ≤ 1
  · have hl := rationalLog_le_log hs hs₁
    have hp : 0 ≤ 78*s^4 + 123*s^3 + 61*s^2 - 55*s + 9 := by
      have he : 78*s^4 + 123*s^3 + 61*s^2 - 55*s + 9 =
          (s-1/4)^2 * (78*s^2 + 162*s + 1097/8) + (55/16)*s + 55/128 := by ring
      rw [he]
      positivity
    have he : (4/25 + (13/25)*s)*(s-1)^2 - s*(s-1-rationalLog s) =
        (s-1)^2 * (78*s^4 + 123*s^3 + 61*s^2 - 55*s + 9) /
          (150*(s+1)^3) := by
      unfold rationalLog
      field_simp
      ring
    calc
      _ ≤ s*(s-1-rationalLog s) := by gcongr
      _ ≤ _ := by
        rw [← sub_nonneg, he]
        positivity
  · have hs₁ : 1 ≤ s := le_of_lt (lt_of_not_ge hs₁)
    have hl := two_mul_sub_div_add_le_log hs₁
    have hp : 0 ≤ 13*s^2 - 8*s + 4 := by
      nlinarith only [sq_nonneg (s - 4/13)]
    have he : (4/25 + (13/25)*s)*(s-1)^2 - s*(s-1-2*(s-1)/(s+1)) =
        (s-1)^2 * (13*s^2 - 8*s + 4) / (25*(s+1)) := by
      field_simp
      ring
    calc
      _ ≤ s*(s-1-2*(s-1)/(s+1)) := by gcongr
      _ ≤ _ := by
        rw [← sub_nonneg, he]
        positivity

/-- The square-root majorant is certified by a positive polynomial decomposition. -/
lemma log_cost_sqrt {s : ℝ} (hs : 0 < s) :
    s * (s - 1 - Real.log s) ≤
      Real.sqrt s * (239/500 + (7/5)*s) * (s-1)^2 := by
  by_cases hs₁ : s ≤ 1
  · let t := Real.sqrt s
    have ht : 0 < t := Real.sqrt_pos.mpr hs
    have ht₂ : t^2 = s := Real.sq_sqrt hs.le
    have ht₁ : t ≤ 1 := by nlinarith
    have hl := rationalLog_le_log ht ht₁
    have hp : 0 ≤ (417/50 : ℝ) - (403/10)*t - (13/5)*t^2 +
        (1047/5)*t^3 + (4617/10)*t^4 + (21717/50)*t^5 + 210*t^6 + 42*t^7 := by
      have he : (417/50 : ℝ) - (403/10)*t - (13/5)*t^2 +
          (1047/5)*t^3 + (4617/10)*t^4 + (21717/50)*t^5 + 210*t^6 + 42*t^7 =
          (t-1/5)^2 * (951397/6250 + (566571/1250)*t + (33099/50)*t^2 +
            (26169/50)*t^3 + (1134/5)*t^4 + 42*t^5) +
            (38424/15625)*t + 175864/78125 := by ring
      rw [he]
      positivity
    have he : (239/500 + (7/5)*t^2)*(t^2-1)^2 -
        t*(t^2-1-2*rationalLog t) =
        (t-1)^2 * ((417/50 : ℝ) - (403/10)*t - (13/5)*t^2 +
          (1047/5)*t^3 + (4617/10)*t^4 + (21717/50)*t^5 + 210*t^6 + 42*t^7) /
          (30*(t+1)^3) := by
      unfold rationalLog
      field_simp
      ring
    have hraw : t*(t^2-1-2*Real.log t) ≤ (239/500+(7/5)*t^2)*(t^2-1)^2 := by
      calc
        _ ≤ t*(t^2-1-2*rationalLog t) := by gcongr
        _ ≤ _ := by
          rw [← sub_nonneg, he]
          positivity
    have h := mul_le_mul_of_nonneg_left hraw ht.le
    have hlog : 2 * Real.log t = Real.log s := by
      rw [← ht₂, Real.log_pow]
      norm_num
    calc
      _ = t * (t*(t^2-1-2*Real.log t)) := by rw [hlog, ← ht₂]; ring
      _ ≤ t*((239/500+(7/5)*t^2)*(t^2-1)^2) := h
      _ = _ := by rw [ht₂]; ring
  · have hs₁ : 1 ≤ s := le_of_lt (lt_of_not_ge hs₁)
    have ht : 1 ≤ Real.sqrt s := by
      simpa using (Real.sqrt_le_sqrt hs₁)
    have hl := Real.one_sub_inv_le_log_of_pos hs
    have hcost : s*(s-1-Real.log s) ≤ (s-1)^2 := by
      have h := mul_le_mul_of_nonneg_left hl hs.le
      have hi : s*s⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
      nlinarith
    have hc : 1 ≤ Real.sqrt s*(239/500+(7/5)*s) := by
      calc
        (1:ℝ) ≤ 239/500+(7/5)*s := by linarith
        _ ≤ Real.sqrt s*(239/500+(7/5)*s) := by
          exact le_mul_of_one_le_left (by positivity) ht
    exact hcost.trans (le_mul_of_one_le_left (sq_nonneg _) hc)

end Submission.Obl.Entropy__absorption_logarithmic_cutoff
