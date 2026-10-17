import Submission.Obl.Entropy__smooth_gaussian_transport.FirstRegularity

open Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- The error in a quadratic expansion, with the linear term specified separately. -/
noncomputable def quadraticError {m : ℕ} (u : E m → ℝ) (x p : E m)
    (A : E m →L[ℝ] E m) (h : E m) : ℝ :=
  u (x + h) - u x - inner ℝ p h - (1 / 2 : ℝ) * inner ℝ (A h) h

private theorem quadratic_increment {m : ℕ} (A : E m →L[ℝ] E m)
    (hA : A.toLinearMap.IsSymmetric) (p q h e : E m) (t : ℝ) :
    inner ℝ q (t • e) - inner ℝ p (t • e) -
        (1 / 2 : ℝ) * (inner ℝ (A (h + t • e)) (h + t • e) - inner ℝ (A h) h) =
      t * inner ℝ (q - p - A h) e - t ^ 2 / 2 * inner ℝ (A e) e := by
  have hcross : inner ℝ (A e) h = inner ℝ (A h) e := by
    rw [hA.apply_clm e h, real_inner_comm]
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, inner_sub_left]
  rw [hcross]
  ring

/-- A quadratic approximation controls every subgradient at an interior point.
The comparison is made in the direction of the subgradient error. -/
theorem subgradient_bound_of_quadratic_error {m : ℕ} {u : E m → ℝ}
    {x p h q : E m} {A : E m →L[ℝ] E m} (hA : A.toLinearMap.IsSymmetric)
    {ε ρ t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) (hinside : ‖h‖ + t < ρ)
    (herror : ∀ z, ‖z‖ < ρ → |quadraticError u x p A z| ≤ ε * ‖z‖ ^ 2)
    (hq : IsSubgradient u (x + h) q) :
    t * ‖q - p - A h‖ ≤ ‖A‖ / 2 * t ^ 2 + ε * ((‖h‖ + t) ^ 2 + ‖h‖ ^ 2) := by
  let g := q - p - A h
  by_cases hg : g = 0
  · change t * ‖g‖ ≤ _
    rw [hg, norm_zero, mul_zero]
    positivity
  let e := ‖g‖⁻¹ • g
  have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg
  have he : ‖e‖ = 1 := by
    dsimp [e]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hgpos)]
    exact inv_mul_cancel₀ hgpos.ne'
  have hge : inner ℝ g e = ‖g‖ := by
    dsimp [e]
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hstep : ‖t • e‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, he, mul_one]
  have hsmall : ‖h‖ < ρ := by linarith
  have hsmall' : ‖h + t • e‖ < ρ :=
    (norm_add_le _ _).trans_lt (by simpa only [hstep] using hinside)
  have herr := abs_le.mp (herror h hsmall)
  have herr' := abs_le.mp (herror (h + t • e) hsmall')
  have hs := hq (x + (h + t • e))
  have hsub : x + (h + t • e) - (x + h) = t • e := by abel
  rw [hsub] at hs
  have hincr := quadratic_increment A hA p q h e t
  have hlin : inner ℝ (q - p - A h) e = ‖g‖ := hge
  rw [hlin] at hincr
  have hbound : inner ℝ (A e) e ≤ ‖A‖ := by
    calc
      _ ≤ ‖A e‖ * ‖e‖ := real_inner_le_norm _ _
      _ = ‖A e‖ := by rw [he, mul_one]
      _ ≤ ‖A‖ * ‖e‖ := A.le_opNorm e
      _ = ‖A‖ := by rw [he, mul_one]
  have hnorm : ‖h + t • e‖ ^ 2 ≤ (‖h‖ + t) ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) _
    simpa only [hstep] using norm_add_le h (t • e)
  have herror_bound := mul_le_mul_of_nonneg_left hnorm hε
  have hquadratic_bound := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ t ^ 2 / 2)
  dsimp [quadraticError] at herr herr'
  rw [inner_add_right, real_inner_smul_right] at herr'
  simp only [real_inner_smul_right] at hincr hs
  change t * ‖g‖ ≤ _
  nlinarith [herr.1, herr'.2]

/-- For a convex differentiable function, a quadratic expansion with a little-o
remainder differentiates its gradient. -/
theorem hasFDerivAt_gradient_of_quadratic_approximation {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hd : Differentiable ℝ u) {x : E m}
    {A : E m →L[ℝ] E m} (hA : A.toLinearMap.IsSymmetric)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ h : E m, ‖h‖ < ρ → |quadraticError u x (gradient u x) A h| ≤ ε * ‖h‖ ^ 2) :
    HasFDerivAt (gradient u) A x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  let η := min 1 (c / (‖A‖ + 1))
  have hη : 0 < η := lt_min (by norm_num) (div_pos hc (by positivity))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hAη : ‖A‖ * η ≤ c := by
    have hηc : η * (‖A‖ + 1) ≤ c :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    nlinarith
  let ε := c * η / 10
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨ρ, hρ, herror⟩ := happrox ε hε
  have hnear : ∀ᶠ h : E m in 𝓝 0, ‖h‖ < ρ / 2 := by
    filter_upwards [Metric.ball_mem_nhds (0 : E m) (by positivity : 0 < ρ / 2)] with h hh
    simpa only [Metric.mem_ball, dist_zero_right] using hh
  filter_upwards [hnear] with h hh
  by_cases hz : h = 0
  · simp [hz]
  have hr : 0 < ‖h‖ := norm_pos_iff.mpr hz
  let t := η * ‖h‖
  have ht : 0 < t := mul_pos hη hr
  have htr : t ≤ ‖h‖ := by
    dsimp [t]
    exact (mul_le_mul_of_nonneg_right hη1 hr.le).trans_eq (one_mul _)
  have hin : ‖h‖ + t < ρ := by linarith
  have hb := subgradient_bound_of_quadratic_error hA hε.le ht hin herror
    (convex_gradient_support hu (hd (x + h)))
  have hsq : (‖h‖ + t) ^ 2 + ‖h‖ ^ 2 ≤ 5 * ‖h‖ ^ 2 := by
    have hs : (‖h‖ + t) ^ 2 ≤ (2 * ‖h‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    nlinarith
  have hquad : ‖A‖ / 2 * t ^ 2 ≤ c * η / 2 * ‖h‖ ^ 2 := by
    calc
      _ = (‖A‖ * η) * (η / 2 * ‖h‖ ^ 2) := by dsimp [t]; ring
      _ ≤ c * (η / 2 * ‖h‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hAη (by positivity)
      _ = _ := by ring
  have herr : ε * ((‖h‖ + t) ^ 2 + ‖h‖ ^ 2) ≤ c * η / 2 * ‖h‖ ^ 2 := by
    calc
      _ ≤ ε * (5 * ‖h‖ ^ 2) := mul_le_mul_of_nonneg_left hsq hε.le
      _ = _ := by dsimp [ε]; ring
  apply le_of_mul_le_mul_left (a := t) _ ht
  calc
    _ ≤ ‖A‖ / 2 * t ^ 2 + ε * ((‖h‖ + t) ^ 2 + ‖h‖ ^ 2) := hb
    _ ≤ c * η / 2 * ‖h‖ ^ 2 + c * η / 2 * ‖h‖ ^ 2 := add_le_add hquad herr
    _ = t * (c * ‖h‖) := by dsimp [t]; ring

/-- A continuous field of quadratic approximations gives a twice continuously
differentiable convex potential. -/
theorem contDiff_two_of_quadratic_approximation {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hd : Differentiable ℝ u)
    {A : E m → E m →L[ℝ] E m} (hA : ∀ x, (A x).toLinearMap.IsSymmetric)
    (hAc : Continuous A)
    (happrox : ∀ (x : E m) (ε : ℝ), 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ h : E m, ‖h‖ < ρ → |quadraticError u x (gradient u x) (A x) h| ≤ ε * ‖h‖ ^ 2) :
    ContDiff ℝ 2 u := by
  have hg : ContDiff ℝ 1 (gradient u) := contDiff_one_iff_hasFDerivAt.mpr
    ⟨A, hAc, fun x => hasFDerivAt_gradient_of_quadratic_approximation hu hd (hA x) (happrox x)⟩
  apply (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
  refine ⟨fun x => innerSL ℝ (gradient u x), (innerSL ℝ).contDiff.comp hg, ?_⟩
  intro x
  convert! (hd x).hasFDerivAt using 1
  exact toDual_gradient

end Submission.Obl.Entropy__smooth_gaussian_transport
