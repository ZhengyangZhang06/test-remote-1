import Submission.Lib.EntropyTools.Remainder

namespace Submission.Obl.Entropy__equality_cases

open Submission.Lib.EntropyTools

/-- The cutoff in the strict remainder is uniformly positive on a bounded interval. -/
theorem rigidityCutoff_ge_tenth {a : ℝ} (ha : 0 ≤ a) (ha100 : a ≤ 100) :
    (1 : ℝ) / 10 ≤ rigidityCutoff a := by
  unfold rigidityCutoff
  split_ifs with h
  · norm_num
  · have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr (lt_of_le_of_ne ha (Ne.symm h))
    have hs10 : Real.sqrt a ≤ 10 := by
      nlinarith [Real.sq_sqrt ha]
    apply le_min (by norm_num)
    apply (le_div_iff₀ (by positivity : 0 < 25 * Real.sqrt a)).mpr
    nlinarith

/-- On a fixed bounded interval, the remainder controls squared distance from one. -/
theorem rigidityWeight_controls_square {a : ℝ} (ha : 0 ≤ a) (ha100 : a ≤ 100) :
    (a - 1) ^ 2 ≤ 10000 * rigidityWeight a := by
  have hd : 0 < 37 + 3 * a := by positivity
  have hfirst : 3 / 337 * (a - 1) ^ 2 ≤ 3 * (a - 1) ^ 2 / (37 + 3 * a) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [sq_nonneg (a - 1), mul_nonneg (sq_nonneg (a - 1)) (show 0 ≤ 100 - a by linarith)]
  have hsecond : (3 : ℝ) / 20 ≤ 3 / 20 + (49 / 100) * (37 / (37 + 3 * a)) := by
    exact le_add_of_nonneg_right (by positivity)
  have hcut := rigidityCutoff_ge_tenth ha ha100
  have h := mul_le_mul
    (mul_le_mul hfirst hsecond (by positivity) (by positivity)) hcut
    (by positivity) (by positivity)
  unfold rigidityWeight
  nlinarith [sq_nonneg (a - 1)]

/-- A coefficient far out on the positive axis has a fixed positive remainder. -/
theorem rigidityWeight_ge_half {a : ℝ} (ha : 100 ≤ a) :
    (1 : ℝ) / 2 ≤ rigidityWeight a := by
  have ha0 : 0 < a := by linarith
  have hd : 0 < 37 + 3 * a := by positivity
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hs10 : 10 ≤ Real.sqrt a := by nlinarith [Real.sq_sqrt ha0.le]
  have hfirst : a / 2 ≤ 3 * (a - 1) ^ 2 / (37 + 3 * a) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [mul_nonneg (show 0 ≤ a - 100 by linarith) (show 0 ≤ a by linarith)]
  have hsecond : (3 : ℝ) / 20 ≤ 3 / 20 + (49 / 100) * (37 / (37 + 3 * a)) := by
    exact le_add_of_nonneg_right (by positivity)
  have hcut : (Real.sqrt a)⁻¹ ≤ rigidityCutoff a := by
    unfold rigidityCutoff
    rw [if_neg ha0.ne']
    apply le_min
    · rw [inv_eq_one_div]
      exact (div_le_iff₀ hs).mpr (by nlinarith)
    · rw [inv_eq_one_div]
      apply (div_le_div_iff₀ hs (by positivity : 0 < 25 * Real.sqrt a)).mpr
      nlinarith
  have h := mul_le_mul
    (mul_le_mul hfirst hsecond (by positivity) (by positivity)) hcut
    (by positivity) (by positivity)
  have hsmall : (1 : ℝ) / 2 ≤ (a / 2 * (3 / 20)) * (Real.sqrt a)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ hs).mpr
    nlinarith [Real.sq_sqrt ha0.le,
      mul_nonneg (show 0 ≤ Real.sqrt a - 10 by linarith) (show 0 ≤ Real.sqrt a by positivity)]
  exact hsmall.trans h

/-- Vanishing strict remainder forces each nonnegative scalar parameter to one. -/
theorem tendsto_one_of_rigidityWeight {α : Type*} {l : Filter α}
    (u : α → ℝ) (hu : ∀ n, 0 ≤ u n)
    (h : Filter.Tendsto (fun n => rigidityWeight (u n)) l (nhds 0)) :
    Filter.Tendsto u l (nhds 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsmall := h.eventually (gt_mem_nhds
    (show (0 : ℝ) < min (1 / 2) (ε ^ 2 / 10000) by positivity))
  filter_upwards [hsmall] with n hn
  have hwsmall : rigidityWeight (u n) < 1 / 2 := (lt_min_iff.mp hn).1
  have hu100 : u n ≤ 100 := by
    by_contra hn100
    have := rigidityWeight_ge_half (le_of_lt (lt_of_not_ge hn100))
    linarith
  have hcontrol := rigidityWeight_controls_square (hu n) hu100
  have hsmall' := (lt_min_iff.mp hn).2
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> nlinarith

/-- When a finite sum of the nonnegative weights vanishes, every parameter tends to one. -/
theorem tendsto_one_of_sum_rigidityWeight {α ι : Type*} [Fintype ι]
    {l : Filter α} (u : α → ι → ℝ) (hu : ∀ n i, 0 ≤ u n i)
    (h : Filter.Tendsto (fun n => ∑ i, rigidityWeight (u n i)) l (nhds 0))
    (i : ι) : Filter.Tendsto (fun n => u n i) l (nhds 1) := by
  apply tendsto_one_of_rigidityWeight _ (fun n => hu n i)
  apply squeeze_zero (fun n => rigidityWeight_nonneg (hu n i)) _ h
  intro n
  exact Finset.single_le_sum (fun j _ => rigidityWeight_nonneg (hu n j)) (Finset.mem_univ i)

end Submission.Obl.Entropy__equality_cases
