import Submission.Obl.Entropy__smooth_gaussian_transport.GaussianDerivatives

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

private theorem power_gaussian_bounded (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 ≤ r → r ^ k * Real.exp (-r ^ 2 / 2) ≤ C := by
  let f : ZeroAtInftyContinuousMap ℝ ℝ := {
    toFun := fun r => |r| ^ k * Real.exp (-(1 / 2 : ℝ) * r ^ 2)
    continuous_toFun := by fun_prop
    zero_at_infty' := by
      simpa only [Real.rpow_natCast] using
        (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (by norm_num : (0 : ℝ) < 1 / 2) (k : ℝ)) }
  obtain ⟨C, hC, hb⟩ := f.isBounded_range.exists_pos_norm_le
  refine ⟨C, hC, fun r hr => ?_⟩
  have hh := hb (f r) (mem_range_self r)
  change ‖|r| ^ k * Real.exp (-(1 / 2 : ℝ) * r ^ 2)‖ ≤ C at hh
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg hr] at hh
  convert! hh using 1 <;> congr 2 <;> ring

private theorem polynomial_gaussian_bounded (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 ≤ r →
      r ^ k * (1 + r) ^ n * Real.exp (-r ^ 2 / 2) ≤ C := by
  obtain ⟨B, hB, hb⟩ := power_gaussian_bounded (k + n)
  refine ⟨2 ^ n * (1 + B), by positivity, ?_⟩
  intro r hr
  by_cases hr1 : r ≤ 1
  · have hk := pow_le_one₀ hr hr1 (n := k)
    have hn : (1 + r) ^ n ≤ (2 : ℝ) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
    have he : Real.exp (-r ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg r])
    calc
      _ ≤ 1 * 2 ^ n * 1 := by gcongr
      _ ≤ 2 ^ n * (1 + B) := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]
  · have hn : (1 + r) ^ n ≤ (2 * r) ^ n :=
      pow_le_pow_left₀ (by positivity) (by linarith) n
    calc
      _ ≤ r ^ k * (2 * r) ^ n * Real.exp (-r ^ 2 / 2) := by gcongr
      _ = 2 ^ n * (r ^ (k + n) * Real.exp (-r ^ 2 / 2)) := by rw [mul_pow, pow_add]; ring
      _ ≤ 2 ^ n * B := mul_le_mul_of_nonneg_left (hb r hr) (by positivity)
      _ ≤ 2 ^ n * (1 + B) := by gcongr; linarith

/-- The standard Euclidean Gaussian, with all polynomially weighted derivative
bounds, as a Schwartz function. -/
noncomputable def gaussianSchwartz (m : ℕ) : SchwartzMap (E m) ℝ where
  toFun := Submission.Lib.EntropyRemainder.gaussianDensity
  smooth' := Submission.Lib.EntropyRemainder.gaussianDensity_contDiff
  decay' := by
    intro k n
    obtain ⟨C, hC, hb⟩ := gaussianDensity_derivative_bound (m := m) n
    obtain ⟨B, hB, hpoly⟩ := polynomial_gaussian_bounded k n
    let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ ^ m
    have hc : 0 < c := by dsimp [c]; positivity
    refine ⟨C * c * B, fun x => ?_⟩
    calc
      _ ≤ ‖x‖ ^ k * (C * (1 + ‖x‖) ^ n * Submission.Lib.EntropyRemainder.gaussianDensity x) := by
        exact mul_le_mul_of_nonneg_left (hb x) (by positivity)
      _ = C * c * (‖x‖ ^ k * (1 + ‖x‖) ^ n * Real.exp (-‖x‖ ^ 2 / 2)) := by
        dsimp [Submission.Lib.EntropyRemainder.gaussianDensity, c]
        ring
      _ ≤ C * c * B := mul_le_mul_of_nonneg_left (hpoly ‖x‖ (norm_nonneg x)) (mul_nonneg hC.le hc.le)

theorem gaussianDensity_weighted_derivative_integrable {m : ℕ} (k n : ℕ) :
    Integrable (fun x : E m => ‖x‖ ^ k *
      ‖iteratedFDeriv ℝ n Submission.Lib.EntropyRemainder.gaussianDensity x‖) volume :=
  (gaussianSchwartz m).integrable_pow_mul_iteratedFDeriv volume k n

end Submission.Obl.Entropy__smooth_gaussian_transport
