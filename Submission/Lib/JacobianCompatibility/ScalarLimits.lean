import Mathlib

/-! Rescaling scalar Taylor remainders uniformly on bounded sets. -/

namespace Submission.Lib.JacobianCompatibility

open Filter Set Asymptotics
open scoped Topology

/-- A scalar remainder of order `o(t^k)` vanishes after homogeneous rescaling,
uniformly when the second argument stays bounded. -/
theorem tendstoUniformlyOn_div_pow_of_isLittleO
    {f : ℝ → ℝ} {k : ℕ} (hf : f =o[𝓝 (0 : ℝ)] fun t ↦ t ^ k)
    {R : ℝ} (hR : 0 ≤ R) :
    TendstoUniformlyOn (fun t x ↦ (t ^ k)⁻¹ * f (t * x)) (fun _ ↦ 0)
      (𝓝[≠] (0 : ℝ)) (Metric.closedBall 0 R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let c : ℝ := ε / (2 * (R ^ k + 1))
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff.mp (hf.bound hc)
  have hsmall : ∀ᶠ t : ℝ in 𝓝[≠] 0, ‖t‖ < δ / (R + 1) :=
    nhdsWithin_le_nhds <| by
      simpa only [Metric.ball, dist_zero_right] using
        Metric.ball_mem_nhds (0 : ℝ) (show 0 < δ / (R + 1) by positivity)
  filter_upwards [hsmall, self_mem_nhdsWithin] with t ht ht0 x hx
  have htne : t ≠ 0 := ht0
  have hxR : ‖x‖ ≤ R := by simpa using hx
  have htx : dist (t * x) 0 < δ := by
    rw [dist_zero_right, norm_mul]
    calc
      ‖t‖ * ‖x‖ ≤ ‖t‖ * (R + 1) := by gcongr; linarith
      _ < δ := (lt_div_iff₀ (by positivity)).mp ht
  have hb := hbound htx
  rw [dist_zero_left, norm_mul, norm_inv]
  calc
    ‖t ^ k‖⁻¹ * ‖f (t * x)‖ ≤ ‖t ^ k‖⁻¹ * (c * ‖(t * x) ^ k‖) := by
      gcongr
    _ = c * ‖x‖ ^ k := by
      rw [mul_pow, norm_mul, norm_pow, norm_pow]
      have htpos : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr htne
      field_simp
    _ ≤ c * R ^ k := by gcongr
    _ < ε := by
      dsimp [c]
      have hpow : 0 ≤ R ^ k := by positivity
      have : ε * R ^ k / (2 * (R ^ k + 1)) < ε := by
        apply (div_lt_iff₀ (by positivity)).mpr
        nlinarith
      simpa only [div_mul_eq_mul_div] using this

/-- Homogeneous scalar Taylor coefficients are uniform limits after rescaling. -/
theorem tendstoUniformlyOn_div_pow_of_taylor
    {f : ℝ → ℝ} {k : ℕ} {c : ℝ}
    (hf : (fun t ↦ f t - c * t ^ k) =o[𝓝 (0 : ℝ)] fun t ↦ t ^ k)
    {R : ℝ} (hR : 0 ≤ R) :
    TendstoUniformlyOn (fun t x ↦ (t ^ k)⁻¹ * f (t * x)) (fun x ↦ c * x ^ k)
      (𝓝[≠] (0 : ℝ)) (Metric.closedBall 0 R) := by
  have hh := tendstoUniformlyOn_div_pow_of_isLittleO hf hR
  rw [Metric.tendstoUniformlyOn_iff] at hh ⊢
  intro ε hε
  filter_upwards [hh ε hε, self_mem_nhdsWithin] with t ht ht0 x hx
  have htne : t ≠ 0 := ht0
  have heq : (t ^ k)⁻¹ * (f (t * x) - c * (t * x) ^ k) =
      (t ^ k)⁻¹ * f (t * x) - c * x ^ k := by
    rw [mul_pow]
    field_simp
  simpa only [dist_zero_left, heq, Real.dist_eq, Real.norm_eq_abs, abs_sub_comm]
    using ht x hx

/-- The first antisymmetric difference extracts the first derivative. -/
theorem odd_difference_isLittleO {q : ℝ → ℝ} {c : ℝ}
    (hq : HasDerivAt q c 0) :
    (fun t ↦ (q t - q (-t)) - (2 * c) * t ^ 1) =o[𝓝 (0 : ℝ)] fun t ↦ t ^ 1 := by
  have h := hq.isLittleO
  simp only [sub_zero, smul_eq_mul] at h
  have hn := h.comp_tendsto (show Tendsto (fun t : ℝ ↦ -t) (𝓝 0) (𝓝 0) by
    simpa using continuous_neg.tendsto (0 : ℝ))
  simp only [Function.comp_def] at hn
  have hn' : (fun t ↦ q (-t) - q 0 - -t * c) =o[𝓝 (0 : ℝ)] fun t ↦ t := by
    simpa only [neg_neg] using hn.neg_right
  exact (h.sub hn').congr (fun t ↦ by ring) (fun t ↦ by ring)

/-- The second symmetric difference extracts the second derivative. -/
theorem even_difference_isLittleO {q : ℝ → ℝ}
    (hq : ContDiff ℝ 2 q) :
    (fun t ↦ (q t + q (-t) - 2 * q 0) - deriv (deriv q) 0 * t ^ 2)
      =o[𝓝 (0 : ℝ)] fun t ↦ t ^ 2 := by
  have h := taylor_isLittleO_univ (x₀ := 0) hq
  have htaylor : ∀ t : ℝ, taylorWithinEval q 2 univ 0 t =
      q 0 + deriv q 0 * t + deriv (deriv q) 0 * t ^ 2 / 2 := by
    intro t
    rw [taylorWithinEval_succ q 1, taylorWithinEval_succ q 0, taylor_within_zero_eval]
    simp only [iteratedDerivWithin_univ, iteratedDeriv_succ, iteratedDeriv_zero,
      Nat.cast_zero, Nat.cast_one, Nat.factorial_zero, Nat.factorial_one,
      zero_add, one_mul, inv_one, sub_zero, pow_one, smul_eq_mul]
    ring
  simp only [htaylor, sub_zero] at h
  have hn := h.comp_tendsto (show Tendsto (fun t : ℝ ↦ -t) (𝓝 0) (𝓝 0) by
    simpa using continuous_neg.tendsto (0 : ℝ))
  simp only [Function.comp_def, neg_sq] at hn
  exact (h.add hn).congr (fun t ↦ by ring) (fun t ↦ rfl)

end Submission.Lib.JacobianCompatibility
