import Submission.Obl.Entropy__smooth_approximation.Limits

open MeasureTheory Filter Asymptotics
open scoped Topology

namespace Submission.Obl.Entropy__smooth_approximation

/-- Exponential radial tails are integrable in every finite dimension. -/
lemma integrable_exp_neg_norm {m : ℕ} {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : E m => Real.exp (-a * ‖x‖)) volume := by
  let r : ℝ := Module.finrank ℝ (E m) + 1
  have hr : (Module.finrank ℝ (E m) : ℝ) < r := by dsimp [r]; linarith
  have hi : Integrable (fun x : E m => (1 + ‖x‖) ^ (-r)) volume :=
    integrable_one_add_norm hr
  have ht : Tendsto (fun x : E m => 1 + ‖x‖) (cocompact (E m)) atTop :=
    tendsto_atTop_add_const_left _ 1 tendsto_norm_cocompact_atTop
  have ho := ((isLittleO_exp_neg_mul_rpow_atTop ha (-r)).comp_tendsto ht).isBigO
  have hb : (fun x : E m => Real.exp (-a * ‖x‖)) =O[cocompact (E m)]
      (fun x : E m => (1 + ‖x‖) ^ (-r)) := by
    apply (ho.const_mul_left (Real.exp a)).congr_left
    intro x
    simp only [Function.comp_apply, ← Real.exp_add]
    congr 1
    ring
  exact (show Continuous (fun x : E m => Real.exp (-a * ‖x‖)) by fun_prop).locallyIntegrable
    |>.integrable_of_isBigO_cocompact hb (hi.integrableAtFilter _)

/-- A quadratic factor can be absorbed by halving the exponential decay rate. -/
lemma quadratic_exp_bound {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) :
    Real.exp (-a * r) * (1 + r ^ 2) ≤ (1 + 8 / a ^ 2) * Real.exp (-(a / 2) * r) := by
  have he := Real.pow_div_factorial_le_exp (a * r / 2) (by positivity) 2
  norm_num at he
  have hp : 0 < Real.exp (-(a / 2) * r) := Real.exp_pos _
  have heq : Real.exp (a * r / 2) * Real.exp (-(a / 2) * r) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  have hquad : r ^ 2 * Real.exp (-(a / 2) * r) ≤ 8 / a ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right he hp.le
    rw [heq] at hh
    apply (le_div_iff₀ (sq_pos_of_pos ha)).2
    nlinarith
  have heq2 : Real.exp (-(a / 2) * r) * Real.exp (-(a / 2) * r) = Real.exp (-a * r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp : Real.exp (-a * r) ≤ Real.exp (-(a / 2) * r) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hquad hp.le
  nlinarith [heq2]

lemma integrable_exp_tail_second {m : ℕ} {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Integrable (fun x : E m => Real.exp (b - a * ‖x‖) * (1 + ‖x‖ ^ 2)) volume := by
  have hi := (integrable_exp_neg_norm (m := m) (half_pos ha)).const_mul
    (Real.exp b * (1 + 8 / a ^ 2))
  apply hi.mono' (by fun_prop)
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [show b - a * ‖x‖ = b + (-a * ‖x‖) by ring, Real.exp_add]
    calc
      Real.exp b * Real.exp (-a * ‖x‖) * (1 + ‖x‖ ^ 2) =
          Real.exp b * (Real.exp (-a * ‖x‖) * (1 + ‖x‖ ^ 2)) := by ring
      _ ≤ Real.exp b * ((1 + 8 / a ^ 2) * Real.exp (-(a / 2) * ‖x‖)) :=
        mul_le_mul_of_nonneg_left (quadratic_exp_bound ha (norm_nonneg _)) (Real.exp_pos b).le
      _ = _ := by ring

/-- Equation (5.2): the entropy integrand is controlled by a slower exponential. -/
lemma entropy_exp_bound {u b : ℝ} (hu : -b ≤ u) :
    |u| * Real.exp (-u) ≤
      (2 + |b| * Real.exp (|b| / 2)) * Real.exp (-u / 2) := by
  have hb0 : 0 ≤ |b| * Real.exp (|b| / 2) := by positivity
  have hhalf : |u| * Real.exp (-u / 2) ≤ 2 + |b| * Real.exp (|b| / 2) := by
    by_cases hu0 : 0 ≤ u
    · rw [abs_of_nonneg hu0]
      have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (u / 2))
        (Real.exp_pos (-u / 2)).le
      have heq : Real.exp (u / 2) * Real.exp (-u / 2) = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero using 2
        ring
      rw [heq] at h
      nlinarith [Real.exp_pos (-u / 2)]
    · have hub : |u| ≤ |b| := by rw [abs_of_neg (lt_of_not_ge hu0)]; linarith [le_abs_self b]
      have he : Real.exp (-u / 2) ≤ Real.exp (|b| / 2) := by
        apply Real.exp_le_exp.mpr
        linarith [le_abs_self b]
      exact (mul_le_mul hub he (Real.exp_pos _).le (abs_nonneg _)).trans (by linarith)
  have h := mul_le_mul_of_nonneg_right hhalf (Real.exp_pos (-u / 2)).le
  have heq : Real.exp (-u / 2) * Real.exp (-u / 2) = Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [mul_assoc, heq] using h

/-- Uniform linear coercivity supplies both majorants in the approximation lemma. -/
theorem approximation_of_linear_tail {m : ℕ} {f : E m → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume) (hmass : ∫ x, f x = 1)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2) volume)
    {U : ℕ → E m → ℝ} (hU : ∀ n, SmoothPotential (U n))
    {a b : ℝ} (ha : 0 < a) (htail : ∀ n x, a * ‖x‖ - b ≤ U n x)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => density (U n) x) atTop (𝓝 (f x))) :
    ∃ V : ℕ → E m → ℝ, (∀ n, Regular (V n)) ∧
      Tendsto (fun n => entropy (density (V n))) atTop (𝓝 (entropy f)) ∧
      (∀ i j, Tendsto (fun n => covariance (density (V n)) i j) atTop
        (𝓝 (covariance f i j))) ∧
      Tendsto (fun n => mean (density (V n))) atTop (𝓝 (mean f)) ∧
      Tendsto (fun n => ∫ x, |density (V n) x - f x|) atTop (𝓝 0) := by
  let c := 2 + |b| * Real.exp (|b| / 2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hiC : Integrable (fun x : E m =>
      c * Real.exp (b / 2) * Real.exp (-(a / 2) * ‖x‖)) volume :=
    (integrable_exp_neg_norm (half_pos ha)).const_mul _
  refine approximation_of_dominated hf0 hf hmass hf2 hU
    (integrable_exp_tail_second ha b) hiC ?_ ?_ hlim
  · intro n x
    apply mul_le_mul_of_nonneg_right _ (by positivity : 0 ≤ 1 + ‖x‖ ^ 2)
    exact Real.exp_le_exp.mpr (by linarith [htail n x])
  · intro n x
    have hlu : -b ≤ U n x := by
      linarith [htail n x, mul_nonneg ha.le (norm_nonneg x)]
    calc
      |density (U n) x * Real.log (density (U n) x)| =
          |U n x| * Real.exp (-U n x) := by
        simp only [density, Real.log_exp, abs_mul, abs_of_pos (Real.exp_pos _), abs_neg]
        ring
      _ ≤ c * Real.exp (-U n x / 2) := entropy_exp_bound hlu
      _ ≤ c * Real.exp (b / 2 - (a / 2) * ‖x‖) := by
        apply mul_le_mul_of_nonneg_left _ hc
        exact Real.exp_le_exp.mpr (by linarith [htail n x])
      _ = c * Real.exp (b / 2) * Real.exp (-(a / 2) * ‖x‖) := by
        simp only [sub_eq_add_neg, Real.exp_add, neg_mul, mul_assoc]

end Submission.Obl.Entropy__smooth_approximation
