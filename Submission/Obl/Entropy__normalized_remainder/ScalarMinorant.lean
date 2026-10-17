import Mathlib
import Submission.Lib.EntropyTools.Remainder

/-!
# The quadratic minorant in Proposition 3.5

These estimates use only the three lower bounds on the scalar function
`p`. Establishing those bounds for the Gaussian transport functions is
left to the paper's scalar certificates.
-/

namespace Submission.Obl.Entropy__normalized_remainder

open MeasureTheory

noncomputable def minorantSlope (u : ℝ) : ℝ := u * Real.sqrt u / 2
noncomputable def minorantLoss (u : ℝ) : ℝ := u ^ 3 / (16 * (23 / 50 - u))

theorem minorantLoss_pos {u : ℝ} (hu : 0 < u) (hu' : u ≤ 13 / 100) :
    0 < minorantLoss u := by
  unfold minorantLoss
  exact div_pos (pow_pos hu _) (mul_pos (by norm_num) (by linarith))

/-- The reciprocal lower bound handles the entire negative half-line. -/
theorem negative_minorant {u a : ℝ} (hu : 0 < u) (hu' : u ≤ 13 / 100) (ha : a ≤ 0) :
    u + minorantSlope u * a ≤ 1 / (7 + a ^ 2) := by
  let x := -(Real.sqrt u * a)
  have hx0 : 0 ≤ x := neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) ha)
  have hx2 : x ^ 2 = u * a ^ 2 := by
    dsimp [x]
    rw [neg_sq, mul_pow, Real.sq_sqrt hu.le]
  have hlin : u + minorantSlope u * a = u * (1 - x / 2) := by
    dsimp [minorantSlope, x]
    ring
  rw [hlin]
  by_cases hx : 2 ≤ x
  · exact (mul_nonpos_of_nonneg_of_nonpos hu.le (by linarith)).trans (by positivity)
  · have hx' : x ≤ 2 := le_of_lt (lt_of_not_ge hx)
    have hpoly : (1 - x / 2) * (x ^ 2 + 7 * u) ≤ 1 := by
      have hsq := mul_nonneg hx0 (sq_nonneg (x - 1))
      have hloss := mul_nonneg (show 0 ≤ 13 / 100 - u by linarith)
        (show 0 ≤ 2 - x by linarith)
      nlinarith
    apply (le_div_iff₀ (show 0 < 7 + a ^ 2 by positivity)).mpr
    calc
      u * (1 - x / 2) * (7 + a ^ 2) = (1 - x / 2) * (u * a ^ 2 + 7 * u) := by ring
      _ = (1 - x / 2) * (x ^ 2 + 7 * u) := by rw [hx2]
      _ ≤ 1 := hpoly

/-- The maximum of the minorant is `23/50`, by completing the square. -/
theorem minorant_le_max {u : ℝ} (hu : 0 < u) (hu' : u ≤ 13 / 100) (a : ℝ) :
    u + minorantSlope u * a - minorantLoss u * a ^ 2 ≤ 23 / 50 := by
  have hd := minorantLoss_pos hu hu'
  have hden : 23 / 50 - u ≠ 0 := ne_of_gt (by linarith)
  have hn : minorantSlope u ^ 2 = 4 * minorantLoss u * (23 / 50 - u) := by
    dsimp [minorantSlope, minorantLoss]
    rw [div_pow, mul_pow, Real.sq_sqrt hu.le]
    field_simp [hden, hu.ne', show 23 - u * 50 ≠ 0 by linarith]
    ring
  have hs := sq_nonneg (2 * minorantLoss u * a - minorantSlope u)
  have hmul : 0 ≤ minorantLoss u *
      (23 / 50 - (u + minorantSlope u * a - minorantLoss u * a ^ 2)) := by
    nlinarith [hs, hn]
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hd).mp hmul)

/-- Three pointwise estimates imply the paper's quadratic lower bound. -/
theorem scalar_quadratic_minorant {p : ℝ → ℝ}
    (hneg : ∀ a, a ≤ 0 → 1 / (7 + a ^ 2) ≤ p a)
    (hpos : ∀ a, 0 ≤ a → 1 / 4 ≤ p a)
    (htail : ∀ a, 4 ≤ a → 23 / 50 ≤ p a)
    {u : ℝ} (hu : 0 < u) (hu' : u ≤ 13 / 100) (a : ℝ) :
    u + minorantSlope u * a - minorantLoss u * a ^ 2 ≤ p a := by
  have hd := (minorantLoss_pos hu hu').le
  by_cases ha : a ≤ 0
  · exact (sub_le_self _ (mul_nonneg hd (sq_nonneg a))).trans
      ((negative_minorant hu hu' ha).trans (hneg a ha))
  · have ha0 : 0 ≤ a := le_of_lt (lt_of_not_ge ha)
    by_cases ha4 : a ≤ 4
    · have hsqrt : Real.sqrt u ≤ 2 / 5 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
      have hn0 : 0 ≤ minorantSlope u := by unfold minorantSlope; positivity
      have hn : minorantSlope u ≤ u / 5 := by
        have h := mul_le_mul_of_nonneg_left hsqrt hu.le
        dsimp [minorantSlope]
        linarith
      have hna := mul_le_mul_of_nonneg_left ha4 hn0
      have hbound : u + minorantSlope u * a - minorantLoss u * a ^ 2 ≤ 1 / 4 := by
        nlinarith [mul_nonneg hd (sq_nonneg a)]
      exact hbound.trans (hpos a ha0)
    · exact (minorant_le_max hu hu' a).trans (htail a (le_of_lt (lt_of_not_ge ha4)))

/-- Averaging the minorant costs only the scalar second moment. -/
theorem integral_scalar_minorant {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {p : ℝ → ℝ} (hp : Integrable p ν)
    (hfirst : Integrable (fun a : ℝ => a) ν)
    (hsecond : Integrable (fun a : ℝ => a ^ 2) ν)
    (hmean : (∫ a, a ∂ν) = 0)
    (hneg : ∀ a, a ≤ 0 → 1 / (7 + a ^ 2) ≤ p a)
    (hpos : ∀ a, 0 ≤ a → 1 / 4 ≤ p a)
    (htail : ∀ a, 4 ≤ a → 23 / 50 ≤ p a)
    {u : ℝ} (hu : 0 < u) (hu' : u ≤ 13 / 100) :
    u - minorantLoss u * (∫ a, a ^ 2 ∂ν) ≤ ∫ a, p a ∂ν := by
  have h := integral_mono
    (((integrable_const u).add (hfirst.const_mul (minorantSlope u))).sub
      (hsecond.const_mul (minorantLoss u))) hp
    (scalar_quadratic_minorant hneg hpos htail hu hu')
  change (∫ a, u + minorantSlope u * a - minorantLoss u * a ^ 2 ∂ν) ≤ ∫ a, p a ∂ν at h
  erw [integral_sub ((integrable_const u).add (hfirst.const_mul (minorantSlope u)))
    (hsecond.const_mul (minorantLoss u)),
    integral_add (integrable_const u) (hfirst.const_mul (minorantSlope u)),
    integral_const_mul, integral_const_mul, hmean] at h
  simpa using h

open Submission.Lib.EntropyTools

/-- The cutoff never exceeds its fixed small-variance value. -/
theorem rigidityCutoff_le (ell : ℝ) : rigidityCutoff ell ≤ 13 / 100 := by
  unfold rigidityCutoff
  split_ifs
  · rfl
  · exact min_le_left _ _

/-- The adaptive cutoff keeps the squared-variance cost uniformly bounded. -/
theorem rigidityCutoff_sq_bound {ell : ℝ} (hell : 0 ≤ ell) :
    ell * rigidityCutoff ell ^ 2 ≤ (32 / 25 : ℝ) ^ 2 := by
  by_cases hzero : ell = 0
  · norm_num [hzero]
  have hsqrt : 0 < Real.sqrt ell := Real.sqrt_pos.mpr (lt_of_le_of_ne hell (Ne.symm hzero))
  have hu : 0 ≤ rigidityCutoff ell := (rigidityCutoff_pos hell).le
  have hcut : rigidityCutoff ell ≤ 32 / (25 * Real.sqrt ell) := by
    simp only [rigidityCutoff, if_neg hzero]
    exact min_le_right _ _
  have hprod : Real.sqrt ell * rigidityCutoff ell ≤ 32 / 25 := by
    have h := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 25) hsqrt)).mp hcut
    nlinarith
  calc
    ell * rigidityCutoff ell ^ 2 = (Real.sqrt ell * rigidityCutoff ell) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hell]
    _ ≤ (32 / 25 : ℝ) ^ 2 := (sq_le_sq₀ (mul_nonneg hsqrt.le hu) (by norm_num)).mpr hprod

/-- At most `311/1000` of the minorant's leading coefficient is lost to variance. -/
theorem minorant_variance_cost {u ell : ℝ} (hu : 0 < u) (hu' : u ≤ 13 / 100)
    (hcut : ell * u ^ 2 ≤ (32 / 25 : ℝ) ^ 2) :
    minorantLoss u * ell ≤ (311 / 1000) * u := by
  have hden : 0 < 16 * (23 / 50 - u) := by nlinarith
  unfold minorantLoss
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  have h := mul_le_mul_of_nonneg_left hcut hu.le
  have h' := mul_nonneg hu.le (show 0 ≤ 13 / 100 - u by linarith)
  nlinarith

/-- The averaged estimate in Proposition 3.5 with the selected cutoff. -/
theorem integral_minorant_cutoff {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {p : ℝ → ℝ} (hp : Integrable p ν)
    (hfirst : Integrable (fun a : ℝ => a) ν)
    (hsecond : Integrable (fun a : ℝ => a ^ 2) ν)
    (hmean : (∫ a, a ∂ν) = 0)
    (hneg : ∀ a, a ≤ 0 → 1 / (7 + a ^ 2) ≤ p a)
    (hpos : ∀ a, 0 ≤ a → 1 / 4 ≤ p a)
    (htail : ∀ a, 4 ≤ a → 23 / 50 ≤ p a)
    {ell r : ℝ} (hell : 0 ≤ ell) (hmoment : (∫ a, a ^ 2 ∂ν) = ell + r) :
    (689 / 1000) * rigidityCutoff ell - minorantLoss (rigidityCutoff ell) * r ≤
      ∫ a, p a ∂ν := by
  have h := integral_scalar_minorant hp hfirst hsecond hmean hneg hpos htail
    (rigidityCutoff_pos hell) (rigidityCutoff_le ell)
  have hc := minorant_variance_cost (rigidityCutoff_pos hell) (rigidityCutoff_le ell)
    (rigidityCutoff_sq_bound hell)
  rw [hmoment] at h
  nlinarith

noncomputable def spectralDefect (ell : ℝ) : ℝ := 3 * (ell - 1) ^ 2 / (37 + 3 * ell)
noncomputable def spectralRho (ell : ℝ) : ℝ := 3 / 20 + (49 / 100) * (37 / (37 + 3 * ell))

theorem spectralDefect_nonneg {ell : ℝ} (hell : 0 ≤ ell) : 0 ≤ spectralDefect ell := by
  unfold spectralDefect
  positivity

theorem spectralRho_nonneg {ell : ℝ} (hell : 0 ≤ ell) : 0 ≤ spectralRho ell := by
  unfold spectralRho
  positivity

theorem spectralRho_le {ell : ℝ} (hell : 0 ≤ ell) : spectralRho ell ≤ 16 / 25 := by
  have h : 37 / (37 + 3 * ell) ≤ 1 :=
    (div_le_iff₀ (by positivity)).mpr (by linarith)
  unfold spectralRho
  linarith

theorem spectralDefect_le_of_one_le {ell : ℝ} (hell : 1 ≤ ell) : spectralDefect ell ≤ ell := by
  unfold spectralDefect
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

theorem spectralDefect_le_of_le_one {ell : ℝ} (hell : 0 ≤ ell) (hell' : ell ≤ 1) :
    spectralDefect ell ≤ 3 / 37 := by
  unfold spectralDefect
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [mul_nonneg hell (show 0 ≤ 1 - ell by linarith)]

/-- A convenient coarse bound for the low-variance case of the loss estimate. -/
theorem minorantLoss_le_half {u : ℝ} (hu : 0 < u) (hu' : u ≤ 13 / 100) :
    minorantLoss u ≤ 1 / 2 := by
  unfold minorantLoss
  apply (div_le_iff₀ (show 0 < 16 * (23 / 50 - u) by nlinarith)).mpr
  have hp : u ^ 3 ≤ 1 := pow_le_one₀ hu.le (by linarith)
  nlinarith

/-- The residual second-moment loss is at most the paper's `27/1000`. -/
theorem weighted_minorantLoss_le {ell : ℝ} (hell : 0 ≤ ell) :
    spectralDefect ell * spectralRho ell * minorantLoss (rigidityCutoff ell) ≤ 27 / 1000 := by
  let u := rigidityCutoff ell
  have hu : 0 < u := rigidityCutoff_pos hell
  have hu' : u ≤ 13 / 100 := rigidityCutoff_le ell
  have hd : 0 ≤ minorantLoss u := (minorantLoss_pos hu hu').le
  have hρ : 0 ≤ spectralRho ell := spectralRho_nonneg hell
  have hρ' := spectralRho_le hell
  change spectralDefect ell * spectralRho ell * minorantLoss u ≤ _
  by_cases hlarge : 1 ≤ ell
  · have hcost := minorant_variance_cost hu hu' (rigidityCutoff_sq_bound hell)
    calc
      spectralDefect ell * spectralRho ell * minorantLoss u ≤
          ell * spectralRho ell * minorantLoss u :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (spectralDefect_le_of_one_le hlarge) hρ) hd
      _ = spectralRho ell * (minorantLoss u * ell) := by ring
      _ ≤ (16 / 25) * ((311 / 1000) * u) :=
        mul_le_mul hρ' hcost (mul_nonneg hd hell) (by norm_num)
      _ ≤ 27 / 1000 := by nlinarith
  · have hH := spectralDefect_le_of_le_one hell (le_of_lt (lt_of_not_ge hlarge))
    calc
      spectralDefect ell * spectralRho ell * minorantLoss u ≤
          (3 / 37) * (16 / 25) * (1 / 2) :=
        mul_le_mul (mul_le_mul hH hρ' hρ (by norm_num))
          (minorantLoss_le_half hu hu') hd (by norm_num)
      _ ≤ 27 / 1000 := by norm_num

/-- The nonlinear-field coefficient in Proposition 3.5 is at most `111/1000`. -/
theorem scalar_y_cost {b h p : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 1 / 2) (hp : 0 < p)
    (hh : |h| ≤ (67 / 100) * Real.sqrt p) :
    (40 / 37 : ℝ) * ((b - 7 / 25) ^ 2 +
      (3 / 40) * h ^ 2 / (4 * (9 / 25) * p)) ≤ 111 / 1000 := by
  have hb2 : (b - 7 / 25) ^ 2 ≤ (7 / 25 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hb (show 0 ≤ 14 / 25 - b by linarith)]
  have hh2 : h ^ 2 ≤ (67 / 100 : ℝ) ^ 2 * p := by
    have hs := (sq_le_sq₀ (abs_nonneg h) (by positivity)).mpr hh
    simpa only [sq_abs, mul_pow, Real.sq_sqrt hp.le] using hs
  have hfrac : (3 / 40 : ℝ) * h ^ 2 / (4 * (9 / 25) * p) ≤
      (5 / 96 : ℝ) * (67 / 100) ^ 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  nlinarith

/-- Once the paper's logarithmic bound is known, the spectral absorption is arithmetic. -/
theorem spectral_absorption_from_log_bound {ell r P cost : ℝ}
    (hell : 0 ≤ ell) (hr : 0 ≤ r)
    (hP : (689 / 1000) * rigidityCutoff ell - minorantLoss (rigidityCutoff ell) * r ≤ P)
    (hcost : cost ≤ (688 / 1000) *
      (spectralDefect ell * spectralRho ell * rigidityCutoff ell)) :
    cost - spectralDefect ell * spectralRho ell * P ≤
      (27 / 1000) * r - rigidityWeight ell / 1000 := by
  have hw : 0 ≤ spectralDefect ell * spectralRho ell :=
    mul_nonneg (spectralDefect_nonneg hell) (spectralRho_nonneg hell)
  have hmean := mul_le_mul_of_nonneg_left hP hw
  have hloss := mul_le_mul_of_nonneg_right (weighted_minorantLoss_le hell) hr
  change cost - spectralDefect ell * spectralRho ell * P ≤
    (27 / 1000) * r -
      (spectralDefect ell * spectralRho ell * rigidityCutoff ell) / 1000
  nlinarith

end Submission.Obl.Entropy__normalized_remainder
