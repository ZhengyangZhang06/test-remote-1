import Submission.Obl.Entropy__smooth_gaussian_transport.SecondRegularity

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Essential oscillation bounds control the classical Hessian at every pair
of points in the same open ball. -/
theorem brenier_hessian_geometric_oscillation {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {K : Set (E m)} (hK : IsCompact K) :
    ∃ β C : ℝ, 0 < β ∧ β < 1 ∧ 0 < C ∧
      ∀ c : E m, Metric.closedBall c 1 ⊆ K → ∀ n : ℕ,
        ∀ x ∈ Metric.ball c (((m : ℝ) + 6)⁻¹ ^ n),
          ∀ y ∈ Metric.ball c (((m : ℝ) + 6)⁻¹ ^ n),
            ‖fderiv ℝ (gradient φ) y - fderiv ℝ (gradient φ) x‖ ≤ C * β ^ n := by
  obtain ⟨β, C, hβ, hβ1, hC, hosc⟩ :=
    brenier_ae_hessian_geometric_oscillation hm hV ha hH hφ hlaw hK
  have hLip := brenier_gradient_lipschitz hm hV ha hH hφ hlaw
  have hd := brenier_gradient_differentiable hm hV ha hH hφ hlaw
  refine ⟨β, 2 * C, hβ, hβ1, by positivity, ?_⟩
  intro c hc n x hx y hy
  have hr : 0 < ((m : ℝ) + 6)⁻¹ ^ n := by positivity
  obtain ⟨z, hz, hzae⟩ := exists_mem_ball_of_ae (hosc c hc n) c hr
  have hb : ∀ᵐ t ∂volume, t ∈ Metric.ball c (((m : ℝ) + 6)⁻¹ ^ n) →
      ‖fderiv ℝ (gradient φ) t - fderiv ℝ (gradient φ) z‖ ≤ C * β ^ n :=
    hzae.mono (fun t ht => ht hz)
  have hp {t : E m} (ht : t ∈ Metric.ball c (((m : ℝ) + 6)⁻¹ ^ n)) :
      ‖fderiv ℝ (gradient φ) t - fderiv ℝ (gradient φ) z‖ ≤ C * β ^ n :=
    fderiv_bound_of_ae_bound hLip hd Metric.isOpen_ball (convex_ball _ _) _
      (mul_nonneg hC.le (pow_nonneg hβ.le n)) hb ht
  calc
    _ ≤ ‖fderiv ℝ (gradient φ) y - fderiv ℝ (gradient φ) z‖ +
        ‖fderiv ℝ (gradient φ) z - fderiv ℝ (gradient φ) x‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C * β ^ n + C * β ^ n := add_le_add (hp hy) (by simpa only [norm_sub_rev] using hp hx)
    _ = _ := by ring

/-- The transport is locally C²,α, with a common positive exponent on each
compact set. -/
theorem brenier_hessian_compact_holder {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {K : Set (E m)} (hK : IsCompact K) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ x ∈ K, ∀ y ∈ K,
        ‖fderiv ℝ (gradient φ) y - fderiv ℝ (gradient φ) x‖ ≤ C * ‖y - x‖ ^ α := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨β, M, hβ, hβ1, hM, hosc⟩ := brenier_hessian_geometric_oscillation hm hV ha hH hφ hlaw
    (isCompact_closedBall (0 : E m) (R + 1))
  have hballs {x : E m} (hx : x ∈ K) : Metric.closedBall x 1 ⊆ Metric.closedBall 0 (R + 1) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖z‖ ≤ ‖z - x‖ + ‖x‖ := by simpa using norm_add_le (z - x) x
      _ ≤ 1 + R := add_le_add (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz) (hKR x hx)
      _ = _ := by ring
  let q : ℝ := ((m : ℝ) + 6)⁻¹
  have hden : 0 < (m : ℝ) + 6 := by positivity
  have hq : 0 < q := inv_pos.mpr hden
  have hq1 : q < 1 := (inv_lt_one₀ hden).mpr (by linarith [Nat.cast_nonneg (α := ℝ) m])
  let α : ℝ := Real.log β / Real.log q
  have hα : 0 < α := div_pos_of_neg_of_neg (Real.log_neg hβ hβ1) (Real.log_neg hq hq1)
  have hqα : q ^ α = β := by
    rw [Real.rpow_def_of_pos hq]
    have he : Real.log q * α = Real.log β := by
      dsimp only [α]
      field_simp [(Real.log_neg hq hq1).ne]
    rw [he, Real.exp_log hβ]
  let γ : ℝ := min α 1
  have hγ : 0 < γ := lt_min hα zero_lt_one
  let L : ℝ := 10 * (1 / Real.sqrt a)
  have hL : 0 < L := by dsimp [L]; positivity
  have hbnd (x : E m) : ‖fderiv ℝ (gradient φ) x‖ ≤ L :=
    norm_fderiv_le_of_lipschitz ℝ (brenier_gradient_lipschitz hm hV ha hH hφ hlaw)
  let C : ℝ := max (M / β ^ 2) (2 * L / q ^ γ)
  have hC : 0 < C := (div_pos hM (sq_pos_of_pos hβ)).trans_le (le_max_left _ _)
  refine ⟨γ, C, hγ, min_le_right _ _, hC, ?_⟩
  intro x hx y _hy
  by_cases he : y = x
  · subst y
    simp only [sub_self, norm_zero, Real.zero_rpow hγ.ne', mul_zero, le_refl]
  have hd : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  by_cases hnear : ‖y - x‖ < q
  · have hd1 : ‖y - x‖ ≤ 1 := hnear.le.trans hq1.le
    obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one hd hd1 hq hq1
    cases n with
    | zero => simp only [zero_add, pow_one] at hnlo; linarith
    | succ n =>
      have hyn : y ∈ Metric.ball x (q ^ n) := by
        rw [Metric.mem_ball, dist_eq_norm]
        exact hnhi.trans_lt (by rw [pow_succ]; exact mul_lt_of_lt_one_right (pow_pos hq _) hq1)
      have hpower : β ^ (n + 1 + 1) ≤ ‖y - x‖ ^ α := by
        rw [← hqα, Real.rpow_pow_comm hq.le]
        exact Real.rpow_le_rpow (pow_nonneg hq.le _) hnlo.le hα.le
      calc
        _ ≤ M * β ^ n := hosc x (hballs hx) n x (Metric.mem_ball_self (pow_pos hq _)) y hyn
        _ = (M / β ^ 2) * β ^ (n + 1 + 1) := by rw [pow_succ, pow_succ]; field_simp; ring
        _ ≤ (M / β ^ 2) * ‖y - x‖ ^ α := mul_le_mul_of_nonneg_left hpower (by positivity)
        _ ≤ (M / β ^ 2) * ‖y - x‖ ^ γ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge hd hd1 (min_le_left _ _)) (by positivity)
        _ ≤ C * ‖y - x‖ ^ γ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _)
  · have hfar : q ≤ ‖y - x‖ := le_of_not_gt hnear
    have hpow : 0 < q ^ γ := Real.rpow_pos_of_pos hq _
    calc
      _ ≤ ‖fderiv ℝ (gradient φ) y‖ + ‖fderiv ℝ (gradient φ) x‖ := norm_sub_le _ _
      _ ≤ 2 * L := by linarith [hbnd y, hbnd x]
      _ = (2 * L / q ^ γ) * q ^ γ := by field_simp
      _ ≤ (2 * L / q ^ γ) * ‖y - x‖ ^ γ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hq.le hfar hγ.le) (by positivity)
      _ ≤ C * ‖y - x‖ ^ γ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) _)

end Submission.Obl.Entropy__smooth_gaussian_transport
