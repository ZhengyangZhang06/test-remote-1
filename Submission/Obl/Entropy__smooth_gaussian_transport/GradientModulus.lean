import Submission.Obl.Entropy__smooth_gaussian_transport.SectionContraction
import Submission.Obl.Entropy__smooth_gaussian_transport.DifferentiableTransport

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem brenier_gradient_geometric_modulus {m : ℕ} (hm : 1 ≤ m) {V φ : E m → ℝ}
    (hV : Continuous V) (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) (x : E m) :
    ∃ κ M δ : ℝ, 0 < κ ∧ κ < 1 ∧ 0 < M ∧ 0 < δ ∧
      ∀ n : ℕ, ∀ y : E m, ‖y - x‖ < δ → ‖y - x‖ ≤ (1 / 2 : ℝ) ^ n →
        ‖gradient φ y - gradient φ x‖ ≤ κ ^ n * M := by
  have hdom : conjugateDomain φ = univ := by
    apply conjugateDomain_eq_univ_of_transport hφ (stdGaussian_absolutelyContinuous m)
    rw [hlaw]
    exact target_support hV
  have hψ := finiteConjugate_convex hdom
  have hψdom := conjugateDomain_finiteConjugate hdom
  have hψMA := brenier_dual_alexandrov_bounds hV hφ hlaw
  obtain ⟨hφ₁, hψ₁⟩ := brenier_contDiff_one hm hV hφ hlaw
  have hdφ := hφ₁.differentiable (by norm_num)
  have hs (y : E m) : IsSubgradient (finiteConjugate φ) (gradient φ y) y :=
    (show IsSubgradient φ y (gradient φ y) from convex_gradient_support hφ (hdφ y)).conjugate hdom
  let v := tilt (fun z => finiteConjugate φ (z + gradient φ x)) x
    (finiteConjugate φ (gradient φ x))
  have hv : ConvexOn ℝ univ v := tilt_convex (translate_convex hψ _) _ _
  have hvdom : conjugateDomain v = univ := tilt_conjugateDomain
    (translate_conjugateDomain hψdom _) _ _
  have hvMA : LocalDensityBounds v := localDensityBounds_tilt
    (hψ.locallyLipschitz.continuous.comp (continuous_id.add continuous_const))
    (translate_conjugateDomain hψdom _)
    (localDensityBounds_translate hψ.locallyLipschitz.continuous hψdom hψMA _) _ _
  have hvnonneg : ∀ z, 0 ≤ v z := by
    intro z
    have h := hs x (z + gradient φ x)
    rw [add_sub_cancel_right] at h
    dsimp only [v, tilt]
    linarith
  have hvzero : v 0 = 0 := by
    simp only [v, tilt, zero_add, inner_zero_right, sub_zero, sub_self]
  obtain ⟨κ, M, hκ, hκ1, hM, hdecay⟩ := exists_section_geometric_decay hm hv hvdom hvMA hvnonneg hvzero
  have hgrad := continuous_gradient_of_contDiff_one hφ₁
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp (hgrad.continuousAt (x := x)) 1 zero_lt_one
  refine ⟨κ, M, δ, hκ, hκ1, hM, hδ, ?_⟩
  intro n y hyδ hyn
  have hnorm : ‖gradient φ y - gradient φ x‖ ≤ 1 := by
    exact (show ‖gradient φ y - gradient φ x‖ < 1 from
      (by simpa only [dist_eq_norm] using hnear (by simpa only [dist_eq_norm] using hyδ))).le
  have hupp : v (gradient φ y - gradient φ x) ≤
      inner ℝ (y - x) (gradient φ y - gradient φ x) := by
    have h := hs y (gradient φ x)
    have heq : gradient φ x - gradient φ y = -(gradient φ y - gradient φ x) := by abel
    rw [heq, inner_neg_right] at h
    simp only [v, tilt, sub_add_cancel, inner_sub_left]
    linarith
  apply hdecay n
  apply hupp.trans
  apply (real_inner_le_norm _ _).trans
  exact (by nlinarith [norm_nonneg (y - x)] :
    ‖y - x‖ * ‖gradient φ y - gradient φ x‖ ≤ ‖y - x‖).trans hyn

/-- The full-space gradient has a positive power modulus at every fixed point. -/
theorem brenier_gradient_pointwise_holder {m : ℕ} (hm : 1 ≤ m) {V φ : E m → ℝ}
    (hV : Continuous V) (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) (x : E m) :
    ∃ α C δ : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ 0 < δ ∧
      ∀ y : E m, ‖y - x‖ < δ →
        ‖gradient φ y - gradient φ x‖ ≤ C * ‖y - x‖ ^ α := by
  obtain ⟨κ, M, δ, hκ, hκ1, hM, hδ, hmod⟩ :=
    brenier_gradient_geometric_modulus hm hV hφ hlaw x
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
  refine ⟨β, M / κ, min δ 1, hβ, min_le_right _ _, div_pos hM hκ,
    lt_min hδ zero_lt_one, ?_⟩
  intro y hy
  by_cases hyx : y = x
  · subst y
    simp only [sub_self, norm_zero, Real.zero_rpow hβ.ne', mul_zero, le_refl]
  have hnorm : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
  have hnorm1 : ‖y - x‖ ≤ 1 := hy.le.trans (min_le_right _ _)
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one hnorm hnorm1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hpower : κ ^ (n + 1) ≤ ‖y - x‖ ^ α := by
    rw [← hκeq, Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact Real.rpow_le_rpow (pow_nonneg (by norm_num) _) hnlo.le hα.le
  calc
    ‖gradient φ y - gradient φ x‖ ≤ κ ^ n * M := hmod n y (hy.trans_le (min_le_left _ _)) hnhi
    _ = (M / κ) * κ ^ (n + 1) := by rw [pow_succ]; field_simp
    _ ≤ (M / κ) * ‖y - x‖ ^ α := mul_le_mul_of_nonneg_left hpower (div_nonneg hM.le hκ.le)
    _ ≤ (M / κ) * ‖y - x‖ ^ β := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hnorm hnorm1 (min_le_left _ _)) (div_nonneg hM.le hκ.le)

end Submission.Obl.Entropy__smooth_gaussian_transport
