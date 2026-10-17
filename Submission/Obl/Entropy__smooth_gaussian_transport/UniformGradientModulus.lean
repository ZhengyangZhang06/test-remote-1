import Submission.Obl.Entropy__smooth_gaussian_transport.CenteredSections
import Submission.Obl.Entropy__smooth_gaussian_transport.DifferentiableTransport

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem brenier_gradient_uniform_geometric_modulus {m : ℕ} (hm : 1 ≤ m) {V φ : E m → ℝ}
    (hV : Continuous V) (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {K : Set (E m)} (hK : IsCompact K) :
    ∃ κ M δ : ℝ, 0 < κ ∧ κ < 1 ∧ 0 < M ∧ 0 < δ ∧
      ∀ x ∈ K, ∀ y ∈ K, ∀ n : ℕ,
        ‖y - x‖ < δ → ‖y - x‖ ≤ (1 / 2 : ℝ) ^ n →
          ‖gradient φ y - gradient φ x‖ ≤ κ ^ n * M := by
  have hdom : conjugateDomain φ = univ := by
    apply conjugateDomain_eq_univ_of_transport hφ (stdGaussian_absolutelyContinuous m)
    rw [hlaw]
    exact target_support hV
  have hψ := finiteConjugate_convex hdom
  have hψdom := conjugateDomain_finiteConjugate hdom
  have hψMA := brenier_dual_alexandrov_bounds hV hφ hlaw
  have hφ₁ := (brenier_contDiff_one hm hV hφ hlaw).1
  have hdφ := hφ₁.differentiable (by norm_num)
  have hs (y : E m) : IsSubgradient (finiteConjugate φ) (gradient φ y) y :=
    (show IsSubgradient φ y (gradient φ y) from convex_gradient_support hφ (hdφ y)).conjugate hdom
  have hgrad := continuous_gradient_of_contDiff_one hφ₁
  obtain ⟨κ, M, hκ, hκ1, hM, hdecay⟩ := uniform_centered_section_decay hm hψ hψdom hψMA
    (hK.image hgrad) hK
  obtain ⟨δ, hδ, hnear⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hgrad.continuousOn) 1 zero_lt_one
  refine ⟨κ, M, δ, hκ, hκ1, hM, hδ, ?_⟩
  intro x hx y hy n hyδ hyn
  have hnorm : ‖gradient φ y - gradient φ x‖ ≤ 1 := by
    have hd := hnear y hy x hx (by simpa only [dist_eq_norm] using hyδ)
    simpa only [dist_eq_norm] using hd.le
  have hupp : centeredPotential (finiteConjugate φ) (gradient φ x) x
      (gradient φ y - gradient φ x) ≤ inner ℝ (y - x) (gradient φ y - gradient φ x) := by
    have h := hs y (gradient φ x)
    have heq : gradient φ x - gradient φ y = -(gradient φ y - gradient φ x) := by abel
    rw [heq, inner_neg_right] at h
    simp only [centeredPotential, tilt, sub_add_cancel, inner_sub_left]
    linarith
  apply hdecay _ (mem_image_of_mem _ hx) x hx (hs x) n
  apply hupp.trans
  apply (real_inner_le_norm _ _).trans
  exact (by nlinarith [norm_nonneg (y - x)] :
    ‖y - x‖ * ‖gradient φ y - gradient φ x‖ ≤ ‖y - x‖).trans hyn

/-- On every compact set, a single positive exponent and constant control all
pairs of values of the transport gradient. -/
theorem brenier_gradient_compact_holder {m : ℕ} (hm : 1 ≤ m) {V φ : E m → ℝ}
    (hV : Continuous V) (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {K : Set (E m)} (hK : IsCompact K) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ x ∈ K, ∀ y ∈ K,
        ‖gradient φ y - gradient φ x‖ ≤ C * ‖y - x‖ ^ α := by
  obtain ⟨κ, M, δ, hκ, hκ1, hM, hδ, hmod⟩ :=
    brenier_gradient_uniform_geometric_modulus hm hV hφ hlaw hK
  have hgrad := continuous_gradient_of_contDiff_one (brenier_contDiff_one hm hV hφ hlaw).1
  obtain ⟨B, hB, hb⟩ := (hK.image hgrad).isBounded.exists_pos_norm_le
  have hlog : Real.log (1 / 2 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  let α : ℝ := Real.log κ / Real.log (1 / 2 : ℝ)
  have hα : 0 < α := div_pos_of_neg_of_neg (Real.log_neg hκ hκ1) hlog
  have hκeq : (1 / 2 : ℝ) ^ α = κ := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have heq : Real.log (1 / 2 : ℝ) * α = Real.log κ := by
      dsimp only [α]
      field_simp
    rw [heq, Real.exp_log hκ]
  let β := min α 1
  have hβ : 0 < β := lt_min hα zero_lt_one
  let ρ := min δ 1
  have hρ : 0 < ρ := lt_min hδ zero_lt_one
  let C := max (M / κ) (2 * B / ρ ^ β)
  have hC : 0 < C := lt_of_lt_of_le (div_pos hM hκ) (le_max_left _ _)
  refine ⟨β, C, hβ, min_le_right _ _, hC, ?_⟩
  intro x hx y hy
  by_cases hyx : y = x
  · subst y
    simp only [sub_self, norm_zero, Real.zero_rpow hβ.ne', mul_zero, le_refl]
  have hnorm : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
  by_cases hnear : ‖y - x‖ < ρ
  · have hnorm1 : ‖y - x‖ ≤ 1 := hnear.le.trans (min_le_right _ _)
    obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one hnorm hnorm1
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have hpower : κ ^ (n + 1) ≤ ‖y - x‖ ^ α := by
      rw [← hκeq, Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact Real.rpow_le_rpow (pow_nonneg (by norm_num) _) hnlo.le hα.le
    calc
      ‖gradient φ y - gradient φ x‖ ≤ κ ^ n * M :=
        hmod x hx y hy n (hnear.trans_le (min_le_left _ _)) hnhi
      _ = (M / κ) * κ ^ (n + 1) := by rw [pow_succ]; field_simp
      _ ≤ (M / κ) * ‖y - x‖ ^ α :=
        mul_le_mul_of_nonneg_left hpower (div_nonneg hM.le hκ.le)
      _ ≤ (M / κ) * ‖y - x‖ ^ β := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hnorm hnorm1 (min_le_left _ _))
        (div_nonneg hM.le hκ.le)
      _ ≤ C * ‖y - x‖ ^ β := mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (norm_nonneg _) _)
  · have hfar : ρ ≤ ‖y - x‖ := le_of_not_gt hnear
    have hpow : 0 < ρ ^ β := Real.rpow_pos_of_pos hρ _
    calc
      ‖gradient φ y - gradient φ x‖ ≤ ‖gradient φ y‖ + ‖gradient φ x‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith [hb _ (mem_image_of_mem _ hx), hb _ (mem_image_of_mem _ hy)]
      _ = (2 * B / ρ ^ β) * ρ ^ β := by field_simp
      _ ≤ (2 * B / ρ ^ β) * ‖y - x‖ ^ β := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hρ.le hfar hβ.le) (div_nonneg (by positivity) hpow.le)
      _ ≤ C * ‖y - x‖ ^ β := mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg (norm_nonneg _) _)

end Submission.Obl.Entropy__smooth_gaussian_transport
