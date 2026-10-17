import Submission.Lib.EntropyTools.Remainder

open Filter
open scoped Topology BigOperators

namespace Submission.Obl.Entropy__centered_slack_transports

open Submission.Lib.EntropyTools

/-- The cutoff has a simple global rational lower bound. -/
theorem rigidityCutoff_lower_bound {a : ℝ} (ha : 0 ≤ a) :
    1 / (100 * (1 + a)) ≤ rigidityCutoff a := by
  unfold rigidityCutoff
  split_ifs with h
  · subst a
    norm_num
  · apply le_min
    · apply (div_le_iff₀ (by positivity : 0 < 100 * (1 + a))).2
      nlinarith
    · have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 (lt_of_le_of_ne ha (Ne.symm h))
      have hsbound : Real.sqrt a ≤ 1 + a := by
        nlinarith [Real.sq_sqrt ha, sq_nonneg (Real.sqrt a - 1)]
      apply (div_le_div_iff₀ (by positivity : 0 < 100 * (1 + a))
        (by positivity : 0 < 25 * Real.sqrt a)).2
      nlinarith

/-- Vanishing weight controls the bounded rational distance from one globally. -/
theorem normalized_distance_sq_le_weight {a : ℝ} (ha : 0 ≤ a) :
    ((a - 1) / (1 + a)) ^ 2 ≤ 10000 * rigidityWeight a := by
  have ht : 0 < 1 + a := by positivity
  have hd : 0 < 37 + 3 * a := by positivity
  have hfirst : 3 * (a - 1) ^ 2 / (37 * (1 + a)) ≤
      3 * (a - 1) ^ 2 / (37 + 3 * a) :=
    div_le_div_of_nonneg_left (by positivity) hd (by linarith)
  have hsecond : (3 : ℝ) / 20 ≤ 3 / 20 + (49 / 100) * (37 / (37 + 3 * a)) := by
    exact le_add_of_nonneg_right (by positivity)
  have hprod := mul_le_mul
    (mul_le_mul hfirst hsecond (by norm_num) (by positivity))
    (rigidityCutoff_lower_bound ha) (by positivity) (by positivity)
  change (3 * (a - 1) ^ 2 / (37 * (1 + a))) * (3 / 20) *
      (1 / (100 * (1 + a))) ≤ rigidityWeight a at hprod
  have hcalc : (3 * (a - 1) ^ 2 / (37 * (1 + a))) * (3 / 20) *
      (1 / (100 * (1 + a))) = (9 / 74000) * ((a - 1) / (1 + a)) ^ 2 := by
    field_simp
    ring
  rw [hcalc] at hprod
  nlinarith [sq_nonneg ((a - 1) / (1 + a))]

/-- A nonnegative sequence with vanishing rigidity weight converges to one. -/
theorem tendsto_one_of_weight (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hw : Tendsto (fun n => rigidityWeight (a n)) atTop (nhds 0)) :
    Tendsto a atTop (nhds 1) := by
  let r := fun n => (a n - 1) / (1 + a n)
  have hs : Tendsto (fun n => (r n) ^ 2) atTop (nhds 0) := by
    apply squeeze_zero (fun n => sq_nonneg (r n))
      (fun n => normalized_distance_sq_le_weight (ha n))
    simpa using hw.const_mul 10000
  have hr : Tendsto r atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := (Real.continuous_sqrt.tendsto 0).comp hs
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using h
  have hid (n : ℕ) : (1 + r n) / (1 - r n) = a n := by
    have ht : 1 + a n ≠ 0 := ne_of_gt (by linarith [ha n])
    have hd : 1 - r n = 2 / (1 + a n) := by
      dsimp [r]
      field_simp
      ring
    rw [hd]
    dsimp [r]
    field_simp
    ring
  have hlim := (hr.const_add 1).div
    (hr.const_sub 1) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  simpa only [Pi.div_def, hid, add_zero, sub_zero, div_one] using hlim

/-- Vanishing of a finite sum of nonnegative rigidity weights forces every
spectral parameter to converge to one. -/
theorem eigenvalue_limits_of_weight {m : ℕ} (ell : ℕ → Fin m → ℝ)
    (hell : ∀ n i, 0 ≤ ell n i)
    (hw : Tendsto (fun n => ∑ i, rigidityWeight (ell n i)) atTop (nhds 0)) :
    ∀ i, Tendsto (fun n => ell n i) atTop (nhds 1) := by
  intro i
  apply tendsto_one_of_weight _ (fun n => hell n i)
  apply squeeze_zero (fun n => rigidityWeight_nonneg (hell n i)) (fun n => ?_) hw
  exact Finset.single_le_sum (fun j _ => rigidityWeight_nonneg (hell n j)) (Finset.mem_univ i)

/-- Both nonnegative terms in the strict remainder vanish with its upper bound. -/
theorem vanish_of_slack {m : ℕ} (energy δ : ℕ → ℝ) (ell : ℕ → Fin m → ℝ)
    (henergy : ∀ n, 0 ≤ energy n) (hell : ∀ n i, 0 ≤ ell n i)
    (hδ : Tendsto δ atTop (nhds 0))
    (hbound : ∀ n, energy n / 500 + (∑ i, rigidityWeight (ell n i)) / 1000 ≤ δ n) :
    Tendsto energy atTop (nhds 0) ∧
      Tendsto (fun n => ∑ i, rigidityWeight (ell n i)) atTop (nhds 0) := by
  have hsum (n : ℕ) : 0 ≤ ∑ i, rigidityWeight (ell n i) :=
    Finset.sum_nonneg fun i _ => rigidityWeight_nonneg (hell n i)
  constructor
  · apply squeeze_zero henergy (fun n => ?_) (by simpa using hδ.const_mul 500)
    have hb := hbound n
    have hs := hsum n
    linarith
  · apply squeeze_zero hsum (fun n => ?_) (by simpa using hδ.const_mul 1000)
    have hb := hbound n
    have he := henergy n
    linarith

end Submission.Obl.Entropy__centered_slack_transports
