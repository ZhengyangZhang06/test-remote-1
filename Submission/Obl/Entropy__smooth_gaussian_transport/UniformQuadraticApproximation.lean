import Submission.Obl.Entropy__smooth_gaussian_transport.QuadraticApproximation

open Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- The error in the symmetric second difference of a quadratic model. -/
noncomputable def centralQuadraticError {m : ℕ} (u : E m → ℝ)
    (A : E m → E m →L[ℝ] E m) (x h : E m) : ℝ :=
  u (x + h) + u (x - h) - 2 * u x - inner ℝ (A x h) h

private theorem norm_le_of_unit_quadratic_bound {m : ℕ} {B : E m →L[ℝ] E m}
    (hB : B.toLinearMap.IsSymmetric) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ v : E m, ‖v‖ = 1 → |inner ℝ (B v) v| ≤ C) : ‖B‖ ≤ C := by
  rw [B.norm_eq_iSup_rayleighQuotient hB]
  apply ciSup_le
  intro v
  by_cases hv : v = 0
  · simpa only [hv, ContinuousLinearMap.rayleighQuotient_apply_zero, abs_zero] using hC
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let e := ‖v‖⁻¹ • v
  have he : ‖e‖ = 1 := by
    dsimp [e]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvpos)]
    exact inv_mul_cancel₀ hvpos.ne'
  rw [← B.rayleigh_smul v (inv_ne_zero hvpos.ne')]
  change |B.rayleighQuotient e| ≤ C
  simpa only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    RCLike.re_to_real, he, one_pow, div_one] using hb e he

/-- Locally uniform second-order expansions of a continuous function have a
continuous quadratic coefficient. No continuity of that coefficient is assumed. -/
theorem continuous_of_uniform_central_quadratic_approximation {m : ℕ} {u : E m → ℝ}
    (hu : Continuous u) {A : E m → E m →L[ℝ] E m}
    (hA : ∀ x, (A x).toLinearMap.IsSymmetric)
    (happrox : ∀ (x : E m) (ε : ℝ), 0 < ε → ∃ r ρ : ℝ, 0 < r ∧ 0 < ρ ∧
      ∀ y : E m, ‖y - x‖ < r → ∀ h : E m, ‖h‖ < ρ →
        |centralQuadraticError u A y h| ≤ ε * ‖h‖ ^ 2) : Continuous A := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨r, ρ, hr, hρ, herr⟩ := happrox x (ε / 8) (by positivity)
  let t := min (ρ / 2) (1 / 2 : ℝ)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have htρ : t < ρ := (min_le_left _ _).trans_lt (half_lt_self hρ)
  have ht1 : t ≤ 1 / 2 := min_le_right _ _
  let K := Metric.closedBall x 2
  have hK : IsCompact K := isCompact_closedBall _ _
  have huc : UniformContinuousOn u K := hK.uniformContinuousOn_of_continuous hu.continuousOn
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.mp huc (ε * t ^ 2 / 16) (by positivity)
  refine ⟨min r (min (1 / 2) δ), lt_min hr (lt_min (by norm_num) hδ), ?_⟩
  intro y hy
  have hyr : ‖y - x‖ < r := (show ‖y - x‖ < min r (min (1 / 2) δ) by
    simpa only [dist_eq_norm] using hy).trans_le (min_le_left _ _)
  have hy1 : ‖y - x‖ < 1 / 2 := (show ‖y - x‖ < min r (min (1 / 2) δ) by
    simpa only [dist_eq_norm] using hy).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hyδ : dist y x < δ := hy.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hxK : x ∈ K := Metric.mem_closedBall_self (by norm_num)
  have hyK : y ∈ K := by
    change dist y x ≤ 2
    rw [dist_eq_norm]
    linarith
  have hb : ‖A y - A x‖ ≤ ε / 2 := by
    have hsym : (A y - A x).toLinearMap.IsSymmetric := (hA y).sub (hA x)
    apply norm_le_of_unit_quadratic_bound (m := m) (B := A y - A x) hsym (half_pos hε).le
    intro v hv
    let h := t • v
    have hhnorm : ‖h‖ = t := by
      dsimp [h]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, hv, mul_one]
    have hhp : ‖h‖ < ρ := hhnorm ▸ htρ
    have hplusy : y + h ∈ K := by
      change ‖y + h - x‖ ≤ 2
      have he : y + h - x = (y - x) + h := by abel
      rw [he]
      exact (norm_add_le _ _).trans (by rw [hhnorm]; linarith)
    have hminusy : y - h ∈ K := by
      change ‖y - h - x‖ ≤ 2
      have he : y - h - x = (y - x) - h := by abel
      rw [he]
      exact (norm_sub_le _ _).trans (by rw [hhnorm]; linarith)
    have hplusx : x + h ∈ K := by
      change ‖x + h - x‖ ≤ 2
      rw [add_sub_cancel_left, hhnorm]
      linarith
    have hminusx : x - h ∈ K := by
      change ‖x - h - x‖ ≤ 2
      have he : x - h - x = -h := by abel
      rw [he, norm_neg, hhnorm]
      linarith
    have hvalplus : |u (y + h) - u (x + h)| < ε * t ^ 2 / 16 := by
      exact hδu (y + h) hplusy (x + h) hplusx (by simpa only [dist_add_right] using hyδ)
    have hvalminus : |u (y - h) - u (x - h)| < ε * t ^ 2 / 16 := by
      exact hδu (y - h) hminusy (x - h) hminusx (by simpa only [dist_sub_right] using hyδ)
    have hvalzero : |u y - u x| < ε * t ^ 2 / 16 := hδu y hyK x hxK hyδ
    have herry := herr y hyr h hhp
    have herrx := herr x (by simpa using hr) h hhp
    rw [hhnorm] at herry herrx
    have hform : |inner ℝ ((A y - A x) h) h| ≤ ε / 2 * t ^ 2 := by
      simp only [sub_apply, inner_sub_left]
      rcases abs_le.mp herry with ⟨herrylo, herryhi⟩
      rcases abs_le.mp herrx with ⟨herrxlo, herrxhi⟩
      rcases abs_lt.mp hvalplus with ⟨hpluslo, hplushi⟩
      rcases abs_lt.mp hvalminus with ⟨hminuslo, hminushi⟩
      rcases abs_lt.mp hvalzero with ⟨hzerolo, hzerohi⟩
      dsimp [centralQuadraticError] at herrylo herryhi herrxlo herrxhi
      rw [abs_le]
      constructor <;> linarith
    apply le_of_mul_le_mul_left (a := t ^ 2) _ (sq_pos_of_pos ht)
    calc
      _ = |inner ℝ ((A y - A x) h) h| := by
        dsimp [h]
        simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
        rw [← mul_assoc, ← sq, abs_mul, abs_of_nonneg (sq_nonneg t)]
      _ ≤ ε / 2 * t ^ 2 := hform
      _ = t ^ 2 * (ε / 2) := mul_comm _ _
  rw [dist_eq_norm]
  exact hb.trans_lt (half_lt_self hε)

/-- Uniform quadratic approximations on neighborhoods give C² regularity of a
convex differentiable function; continuity of the Hessian follows from the errors. -/
theorem contDiff_two_of_uniform_quadratic_approximation {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hd : Differentiable ℝ u)
    {A : E m → E m →L[ℝ] E m} (hA : ∀ x, (A x).toLinearMap.IsSymmetric)
    (happrox : ∀ (x : E m) (ε : ℝ), 0 < ε → ∃ r ρ : ℝ, 0 < r ∧ 0 < ρ ∧
      ∀ y : E m, ‖y - x‖ < r → ∀ h : E m, ‖h‖ < ρ →
        |quadraticError u y (gradient u y) (A y) h| ≤ ε * ‖h‖ ^ 2) :
    ContDiff ℝ 2 u := by
  have hAc : Continuous A := by
    apply continuous_of_uniform_central_quadratic_approximation hd.continuous hA
    intro x ε hε
    obtain ⟨r, ρ, hr, hρ, herr⟩ := happrox x (ε / 2) (half_pos hε)
    refine ⟨r, ρ, hr, hρ, ?_⟩
    intro y hy h hh
    have hplus := herr y hy h hh
    have hminus := herr y hy (-h) (by simpa only [norm_neg] using hh)
    have he : centralQuadraticError u A y h =
        quadraticError u y (gradient u y) (A y) h +
          quadraticError u y (gradient u y) (A y) (-h) := by
      simp only [centralQuadraticError, quadraticError, map_neg, inner_neg_left,
        inner_neg_right, neg_neg, ← sub_eq_add_neg]
      ring
    rw [he]
    calc
      _ ≤ |quadraticError u y (gradient u y) (A y) h| +
          |quadraticError u y (gradient u y) (A y) (-h)| := abs_add_le _ _
      _ ≤ ε / 2 * ‖h‖ ^ 2 + ε / 2 * ‖-h‖ ^ 2 := add_le_add hplus hminus
      _ = ε * ‖h‖ ^ 2 := by rw [norm_neg]; ring
  apply contDiff_two_of_quadratic_approximation hu hd hA hAc
  intro x ε hε
  obtain ⟨r, ρ, hr, hρ, herr⟩ := happrox x ε hε
  exact ⟨ρ, hρ, herr x (by simpa using hr)⟩

end Submission.Obl.Entropy__smooth_gaussian_transport
