import Submission.Obl.Root.LogAbsorption

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set

namespace Submission.Obl.Root.LogAbsorption

/-- The auxiliary function used to establish equation (4.9). -/
noncomputable def logGap (x : ℝ) : ℝ :=
  (239 / 500 + 7 / 5 * x ^ 2) * (1 - x ^ 2) ^ 2 / x -
    (x ^ 2 - 1 - 2 * Real.log x)

noncomputable def gapPolynomial (x : ℝ) : ℝ :=
  -(239 / 500) + 2 * x + 111 / 250 * x ^ 2 - 2 * x ^ 3 - 3483 / 500 * x ^ 4 + 7 * x ^ 6

lemma hasDerivAt_logGap {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt logGap (gapPolynomial x / x ^ 2) x := by
  have h2 := (hasDerivAt_id x).pow 2
  have hn := ((h2.const_mul (7 / 5)).const_add (239 / 500)).mul ((h2.const_sub 1).pow 2)
  convert (hn.div (hasDerivAt_id x) hx).sub
    ((h2.sub_const 1).sub ((Real.hasDerivAt_log hx).const_mul 2)) using 1
  all_goals try rfl
  dsimp [gapPolynomial]
  field_simp [hx]
  ring

lemma logGap_one : logGap 1 = 0 := by norm_num [logGap]

lemma gapPolynomial_nonpos_small {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 5) :
    gapPolynomial x ≤ 0 := by
  have h2 := pow_le_pow_left₀ hx0 hx 2
  have h6 := pow_le_pow_left₀ hx0 hx 6
  dsimp [gapPolynomial]
  nlinarith [pow_nonneg hx0 3, pow_nonneg hx0 4]

noncomputable def tailFactor (x : ℝ) : ℝ :=
  239 / 500 - 761 / 500 * x - 983 / 500 * x ^ 2 + 17 / 500 * x ^ 3 + 7 * x ^ 4 + 7 * x ^ 5

lemma gapPolynomial_factor (x : ℝ) : gapPolynomial x = (x - 1) * tailFactor x := by
  dsimp [gapPolynomial, tailFactor]
  ring

lemma tailFactor_nonneg {x : ℝ} (hx : 3 / 5 ≤ x) : 0 ≤ tailFactor x := by
  have hy : 0 ≤ x - 3 / 5 := sub_nonneg.mpr hx
  have he : tailFactor x = 4936 / 15625 + 21061 / 3125 * (x - 3 / 5) +
      35419 / 1250 * (x - 3 / 5) ^ 2 + 21017 / 500 * (x - 3 / 5) ^ 3 +
      28 * (x - 3 / 5) ^ 4 + 7 * (x - 3 / 5) ^ 5 := by
    dsimp [tailFactor]
    ring
  rw [he]
  positivity

/-- A rational lower bound from the tangent inequality for `log (x/a)`. -/
lemma logGap_nonneg_of_polynomial {x a L : ℝ} (hx : 0 < x) (ha : 0 < a)
    (hL : L ≤ Real.log a)
    (hp : 0 ≤ (239 / 500 + 7 / 5 * x ^ 2) * (1 - x ^ 2) ^ 2 - x ^ 3 +
      (3 + 2 * L) * x - 2 * a) : 0 ≤ logGap x := by
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hx ha)
  rw [inv_div, Real.log_div hx.ne' ha.ne'] at hl
  have hlow : L + 1 - a / x ≤ Real.log x := by linarith
  have he : x * logGap x =
      ((239 / 500 + 7 / 5 * x ^ 2) * (1 - x ^ 2) ^ 2 - x ^ 3 + (3 + 2 * L) * x - 2 * a) +
      2 * x * (Real.log x - (L + 1 - a / x)) := by
    dsimp [logGap]
    field_simp
    ring
  have hn : 0 ≤ x * logGap x := by
    rw [he]
    exact add_nonneg hp (mul_nonneg (by positivity) (sub_nonneg.mpr hlow))
  exact nonneg_of_mul_nonneg_right hn hx

lemma log_half_lower : -(347 / 500 : ℝ) ≤ Real.log (1 / 2) := by
  have h := Real.log_two_lt_d9
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  linarith

lemma log_quarter_lower : -(347 / 250 : ℝ) ≤ Real.log (1 / 4) := by
  have h := log_half_lower
  have he : Real.log (1 / 4 : ℝ) = 2 * Real.log (1 / 2 : ℝ) := by
    rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [he]
  linarith



/-- Exact Bernstein coefficient certificate on `[1/5, 2/5]`. -/
lemma middle_polynomial_left {x : ℝ} (hx : x ∈ Icc (1 / 5 : ℝ) (2 / 5 : ℝ)) :
    0 ≤ (239 / 500 + 7 / 5 * x ^ 2) * (1 - x ^ 2) ^ 2 - x ^ 3 +
      (3 + 2 * (-347 / 250 : ℝ)) * x - 2 * (1 / 4 : ℝ) := by
  let y : ℝ := 5 * x - 1
  have hy : 0 ≤ y := by dsimp [y]; linarith [hx.1]
  have hy' : 0 ≤ 1 - y := by dsimp [y]; linarith [hx.2]
  have he : (239 / 500 + 7 / 5 * x ^ 2) * (1 - x ^ 2) ^ 2 - x ^ 3 +
      (3 + 2 * (-347 / 250 : ℝ)) * x - 2 * (1 / 4 : ℝ) =
      (4521 / 156250 : ℝ) * y ^ 0 * (1 - y) ^ 6 +
      (16844 / 78125 : ℝ) * y ^ 1 * (1 - y) ^ 5 +
      (96377 / 156250 : ℝ) * y ^ 2 * (1 - y) ^ 4 +
      (67878 / 78125 : ℝ) * y ^ 3 * (1 - y) ^ 3 +
      (195401 / 312500 : ℝ) * y ^ 4 * (1 - y) ^ 2 +
      (32411 / 156250 : ℝ) * y ^ 5 * (1 - y) ^ 1 +
      (6541 / 312500 : ℝ) * y ^ 6 * (1 - y) ^ 0 := by
    dsimp [y]
    ring
  rw [he]
  positivity

/-- Exact Bernstein coefficient certificate on `[2/5, 3/5]`. -/
lemma middle_polynomial_right {x : ℝ} (hx : x ∈ Icc (2 / 5 : ℝ) (3 / 5 : ℝ)) :
    0 ≤ (239 / 500 + 7 / 5 * x ^ 2) * (1 - x ^ 2) ^ 2 - x ^ 3 +
      (3 + 2 * (-347 / 500 : ℝ)) * x - 2 * (1 / 2 : ℝ) := by
  let y : ℝ := 5 * x - 2
  have hy : 0 ≤ y := by dsimp [y]; linarith [hx.1]
  have hy' : 0 ≤ 1 - y := by dsimp [y]; linarith [hx.2]
  have he : (239 / 500 + 7 / 5 * x ^ 2) * (1 - x ^ 2) ^ 2 - x ^ 3 +
      (3 + 2 * (-347 / 500 : ℝ)) * x - 2 * (1 / 2 : ℝ) =
      (23791 / 312500 : ℝ) * y ^ 0 * (1 - y) ^ 6 +
      (10196 / 15625 : ℝ) * y ^ 1 * (1 - y) ^ 5 +
      (632141 / 312500 : ℝ) * y ^ 2 * (1 - y) ^ 4 +
      (239469 / 78125 : ℝ) * y ^ 3 * (1 - y) ^ 3 +
      (190909 / 78125 : ℝ) * y ^ 4 * (1 - y) ^ 2 +
      (30569 / 31250 : ℝ) * y ^ 5 * (1 - y) ^ 1 +
      (23973 / 156250 : ℝ) * y ^ 6 * (1 - y) ^ 0 := by
    dsimp [y]
    ring
  rw [he]
  positivity

lemma logGap_nonneg_middle_left {x : ℝ} (hx : x ∈ Icc (1 / 5 : ℝ) (2 / 5)) :
    0 ≤ logGap x :=
  logGap_nonneg_of_polynomial (by linarith [hx.1]) (by norm_num)
    log_quarter_lower (by simpa only [neg_div] using middle_polynomial_left hx)

lemma logGap_nonneg_middle_right {x : ℝ} (hx : x ∈ Icc (2 / 5 : ℝ) (3 / 5)) :
    0 ≤ logGap x :=
  logGap_nonneg_of_polynomial (by linarith [hx.1]) (by norm_num)
    log_half_lower (by simpa only [neg_div] using middle_polynomial_right hx)

lemma logGap_antitone_small : AntitoneOn logGap (Ioc (0 : ℝ) (1 / 5)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun x => gapPolynomial x / x ^ 2)
    (convex_Ioc _ _)
  · intro x hx
    exact (hasDerivAt_logGap hx.1.ne').continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_logGap (interior_subset hx).1.ne').hasDerivWithinAt
  · intro x hx
    have hm := interior_subset hx
    exact div_nonpos_of_nonpos_of_nonneg (gapPolynomial_nonpos_small hm.1.le hm.2) (sq_nonneg x)

lemma logGap_antitone_upper : AntitoneOn logGap (Icc (3 / 5 : ℝ) 1) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun x => gapPolynomial x / x ^ 2)
    (convex_Icc _ _)
  · intro x hx
    exact (hasDerivAt_logGap (by linarith [hx.1])).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_logGap (by have := (interior_subset hx).1; linarith)).hasDerivWithinAt
  · intro x hx
    have hm := interior_subset hx
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg x)
    rw [gapPolynomial_factor]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hm.2) (tailFactor_nonneg hm.1)

lemma logGap_monotone_tail : MonotoneOn logGap (Ici (1 : ℝ)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => gapPolynomial x / x ^ 2)
    (convex_Ici _)
  · intro x hx
    exact (hasDerivAt_logGap (by have : 1 ≤ x := hx; linarith)).continuousAt.continuousWithinAt
  · intro x hx
    have hm : 1 ≤ x := interior_subset hx
    exact (hasDerivAt_logGap (by linarith)).hasDerivWithinAt
  · intro x hx
    have hm : 1 ≤ x := interior_subset hx
    apply div_nonneg _ (sq_nonneg x)
    rw [gapPolynomial_factor]
    exact mul_nonneg (sub_nonneg.mpr hm) (tailFactor_nonneg (by linarith))

/-- Positivity of the paper's scalar auxiliary function, with rational interval certificates. -/
theorem logGap_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ logGap x := by
  by_cases h1 : x ≤ 1 / 5
  · exact (logGap_nonneg_middle_left (x := 1 / 5) (by constructor <;> norm_num)).trans
      (logGap_antitone_small ⟨hx, h1⟩ (by constructor <;> norm_num) h1)
  by_cases h2 : x ≤ 2 / 5
  · exact logGap_nonneg_middle_left ⟨(not_le.mp h1).le, h2⟩
  by_cases h3 : x ≤ 3 / 5
  · exact logGap_nonneg_middle_right ⟨(not_le.mp h2).le, h3⟩
  by_cases h4 : x ≤ 1
  · have h := logGap_antitone_upper ⟨(not_le.mp h3).le, h4⟩ (by constructor <;> norm_num) h4
    rwa [logGap_one] at h
  · have h := logGap_monotone_tail (by simp) (show x ∈ Ici (1 : ℝ) from (not_le.mp h4).le)
      (not_le.mp h4).le
    rwa [logGap_one] at h

/-- The square-root estimate used in the second part of equation (4.8). -/
theorem logCost_div_sqrt_le {s : ℝ} (hs : 0 < s) :
    logCost s / Real.sqrt s ≤ 239 / 500 + 7 / 5 * s := by
  by_cases h1 : s = 1
  · subst s
    rw [logCost_one]
    norm_num
  have hx : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hd : 0 < (1 - s) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm h1))
  have hg := logGap_nonneg hx
  dsimp [logGap] at hg
  rw [Real.sq_sqrt hs.le, Real.log_sqrt hs.le] at hg
  have hb : s - 1 - Real.log s ≤
      (239 / 500 + 7 / 5 * s) * (1 - s) ^ 2 / Real.sqrt s := by linarith
  have hm := (le_div_iff₀ hx).mp hb
  calc
    logCost s / Real.sqrt s = (s - 1 - Real.log s) * Real.sqrt s / (1 - s) ^ 2 := by
      rw [logCost_eq hs h1]
      field_simp
      rw [Real.sq_sqrt hs.le]
      ring
    _ ≤ 239 / 500 + 7 / 5 * s := (div_le_iff₀ hd).mpr hm

/-- The second uniform logarithmic estimate, including zero eigenvalues. -/
theorem logCost_rho_mul_sqrt_le {s lam : ℝ} (hs : 0 < s) (hlam : 0 ≤ lam)
    (hrel : (3 / 40 : ℝ) * lam = 1 / s - 37 / 40) :
    (3 / 40) * logCost s / (3 / 20 + 1813 / 4000 * s) * Real.sqrt lam ≤ (22 / 25 : ℝ) := by
  have hx : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hy : 0 ≤ Real.sqrt lam := Real.sqrt_nonneg _
  have hrho : 0 < (3 / 20 : ℝ) + 1813 / 4000 * s := by positivity
  have hsl : (3 / 40 : ℝ) * s * lam ≤ 1 := by
    have h := congrArg (fun r : ℝ => s * r) hrel
    field_simp [hs.ne'] at h
    nlinarith
  have hsq : ((3 / 40 : ℝ) * Real.sqrt s * Real.sqrt lam) ^ 2 ≤ 3 / 40 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hs.le, Real.sq_sqrt hlam]
    nlinarith
  have hprod : (3 / 40 : ℝ) * Real.sqrt s * Real.sqrt lam ≤ 69 / 250 := by
    nlinarith [sq_nonneg ((3 / 40 : ℝ) * Real.sqrt s * Real.sqrt lam - 69 / 250)]
  have hlog := (div_le_iff₀ hx).mp (logCost_div_sqrt_le hs)
  have hA : 0 ≤ (239 / 500 : ℝ) + 7 / 5 * s := by positivity
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog
    (by norm_num : (0 : ℝ) ≤ 3 / 40)) hy
  have hmul' := mul_le_mul_of_nonneg_right hprod hA
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hrho).mpr
  nlinarith

end Submission.Obl.Root.LogAbsorption
