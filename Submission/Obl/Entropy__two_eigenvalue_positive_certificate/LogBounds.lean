import Mathlib

open Filter Set
open scoped Topology

namespace Submission.Obl.Entropy__two_eigenvalue_positive_certificate

noncomputable def tailTheta (a : ℝ) : ℝ := Real.log (a * Real.sqrt (2 * Real.pi))

/-- A rational enclosure for the logarithmic constant at the positive-tail endpoint. -/
theorem theta_ten : (3221 / 1000 : ℝ) ≤ tailTheta 10 ∧ tailTheta 10 ≤ 1611 / 500 := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  have hl : Real.exp (3221 / 1000) < 1253 / 50 := by
    have he := Real.exp_bound' (x := (221 / 1000 : ℝ)) (by norm_num) (by norm_num)
      (n := 6) (by norm_num)
    norm_num [Finset.sum_range_succ] at he
    have h3 : Real.exp (1 : ℝ) ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := by
      gcongr
      exact Real.exp_one_lt_d9.le
    calc
      _ = Real.exp 1 ^ 3 * Real.exp (221 / 1000) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1 <;> norm_num
      _ ≤ (2.7182818286 : ℝ)^3 *
          ((∑ m ∈ Finset.range 6, (221 / 1000 : ℝ)^m / m.factorial) +
            (221 / 1000 : ℝ)^6 * 7 / (720 * 6)) := by
        gcongr
        norm_num [Finset.sum_range_succ]
        exact he
      _ < _ := by norm_num [Finset.sum_range_succ]
  have hu : (2507 / 100 : ℝ) < Real.exp (1611 / 500) := by
    have he := Real.sum_le_exp_of_nonneg (x := (111 / 500 : ℝ)) (by norm_num) 6
    calc
      _ < (2.7182818283 : ℝ)^3 *
          (∑ m ∈ Finset.range 6, (111 / 500 : ℝ)^m / m.factorial) := by
        norm_num [Finset.sum_range_succ]
      _ ≤ Real.exp 1 ^ 3 * Real.exp (111 / 500) := by
        gcongr
        exact Real.exp_one_gt_d9.le
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1 <;> norm_num
  constructor
  · apply (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < 10 * Real.sqrt (2 * Real.pi))).2
    have hπ := Real.pi_gt_d4
    nlinarith
  · apply (Real.log_le_iff_le_exp (by positivity : (0 : ℝ) < 10 * Real.sqrt (2 * Real.pi))).2
    have hπ := Real.pi_lt_d4
    nlinarith

/-- The derivative of the logarithmic correction. -/
theorem hasDerivAt_tailTheta {a : ℝ} (ha : 0 < a) :
    HasDerivAt tailTheta a⁻¹ a := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  convert! (((hasDerivAt_id a).mul_const (Real.sqrt (2 * Real.pi))).log
    (ne_of_gt (mul_pos ha hs))) using 1
  simp only [id_eq, one_mul]
  field_simp

/-- The logarithmic correction increases throughout the positive tail. -/
theorem theta_lower {a : ℝ} (ha : 10 ≤ a) : 3221 / 1000 ≤ tailTheta a := by
  apply theta_ten.1.trans
  apply Real.log_le_log (by positivity)
  exact mul_le_mul_of_nonneg_right ha (Real.sqrt_nonneg _)

/-- Inverse powers dominate the logarithmic correction uniformly on the tail. -/
theorem weighted_theta_bound (n : ℕ) (c : ℝ)
    (hc : 1 ≤ ((n : ℝ) + 1) * (3221 / 1000 - c)) {a : ℝ} (ha : 10 ≤ a) :
    (tailTheta a - c) / a ^ (n + 1) ≤ (1611 / 500 - c) / 10 ^ (n + 1) := by
  have hd (x : ℝ) (hx : 10 ≤ x) : HasDerivAt
      (fun x => (tailTheta x - c) / x ^ (n + 1))
      ((1 - ((n : ℝ) + 1) * (tailTheta x - c)) / x ^ (n + 2)) x := by
    have hxp : 0 < x := by linarith
    convert! ((hasDerivAt_tailTheta hxp).sub_const c).div
      ((hasDerivAt_id x).pow (n + 1)) (pow_ne_zero _ hxp.ne') using 1
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, Pi.pow_apply, id_eq, mul_one]
    field_simp
    <;> ring
  have hm : AntitoneOn (fun x => (tailTheta x - c) / x ^ (n + 1)) (Ici 10) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 10)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    intro x hx
    have hx' : 10 ≤ x := interior_subset hx
    rw [(hd x hx').deriv]
    apply div_nonpos_of_nonpos_of_nonneg
    · have hh := mul_le_mul_of_nonneg_left (theta_lower hx')
        (by positivity : 0 ≤ (n : ℝ) + 1)
      nlinarith only [hh, hc]
    · positivity
  calc
    _ ≤ (tailTheta 10 - c) / (10 : ℝ) ^ (n + 1) := hm (by norm_num) ha ha
    _ ≤ _ := by gcongr; exact theta_ten.2

end Submission.Obl.Entropy__two_eigenvalue_positive_certificate
