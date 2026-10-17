import Submission.Obl.Entropy__smooth_gaussian_transport.UniformGradientModulus

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

private theorem le_mul_rpow_on_bounded_interval {α D d : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hD : 1 ≤ D) (hd : 0 ≤ d) (hdD : d ≤ D) :
    d ≤ D * d ^ α := by
  rcases hd.eq_or_lt with hd | hd
  · subst d
    simp only [Real.zero_rpow hα.ne', mul_zero, le_refl]
  by_cases hd1 : d ≤ 1
  · calc
      d = d ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ d ^ α := Real.rpow_le_rpow_of_exponent_ge hd hd1 hα1
      _ ≤ D * d ^ α := by nlinarith [Real.rpow_nonneg hd.le α]
  · have hp : 1 ≤ d ^ α := Real.one_le_rpow (le_of_not_ge hd1) hα.le
    nlinarith

/-- A continuously differentiable function of position and transport gradient
has a uniform positive power modulus on each compact set. -/
theorem brenier_smooth_composition_compact_holder {m : ℕ} (hm : 1 ≤ m) {V φ : E m → ℝ}
    (hV : Continuous V) (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {F : E m × E m → ℝ} (hF : ContDiff ℝ 1 F) {K : Set (E m)} (hK : IsCompact K) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ x ∈ K, ∀ y ∈ K,
      |F (y, gradient φ y) - F (x, gradient φ x)| ≤ C * ‖y - x‖ ^ α := by
  obtain ⟨α, A, hα, hα1, hA, hmod⟩ := brenier_gradient_compact_holder hm hV hφ hlaw hK
  have hg := continuous_gradient_of_contDiff_one (brenier_contDiff_one hm hV hφ hlaw).1
  let g : E m → E m × E m := fun x => (x, gradient φ x)
  have hg' : Continuous g := continuous_id.prodMk hg
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (hK.image hg') hF.locallyLipschitz.locallyLipschitzOn
  obtain ⟨B, hB, hb⟩ := hK.isBounded.exists_pos_norm_le
  let D := max 1 (2 * B)
  have hD : 1 ≤ D := le_max_left _ _
  have hC : 0 < ((L : ℝ) + 1) * (D + A) :=
    mul_pos (by positivity) (by linarith)
  refine ⟨α, ((L : ℝ) + 1) * (D + A), hα, hα1, hC, ?_⟩
  intro x hx y hy
  have hdD : ‖y - x‖ ≤ D := by
    have hn := norm_sub_le y x
    have hbD : 2 * B ≤ D := le_max_right _ _
    linarith [hb x hx, hb y hy]
  have hid := le_mul_rpow_on_bounded_interval hα hα1 hD (norm_nonneg (y - x)) hdD
  have hp : 0 ≤ ‖y - x‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  have hd : dist (g y) (g x) ≤ (D + A) * ‖y - x‖ ^ α := by
    change max (dist y x) (dist (gradient φ y) (gradient φ x)) ≤ _
    simp only [dist_eq_norm]
    apply max_le
    · nlinarith
    · have h := hmod x hx y hy
      have hD0 : 0 ≤ D := zero_le_one.trans hD
      nlinarith
  calc
    |F (y, gradient φ y) - F (x, gradient φ x)| = dist (F (g y)) (F (g x)) :=
      (Real.dist_eq _ _).symm
    _ ≤ (L : ℝ) * dist (g y) (g x) :=
      hL.dist_le_mul _ (mem_image_of_mem _ hy) _ (mem_image_of_mem _ hx)
    _ ≤ (L : ℝ) * ((D + A) * ‖y - x‖ ^ α) := mul_le_mul_of_nonneg_left hd L.coe_nonneg
    _ ≤ (((L : ℝ) + 1) * (D + A)) * ‖y - x‖ ^ α := by
      have hDA : 0 ≤ D + A := by linarith
      nlinarith [mul_nonneg hDA hp]

/-- The density in the Alexandrov equation is locally Hölder continuous. -/
theorem brenier_alexandrov_compact_holder_density {m : ℕ} (hm : 1 ≤ m) {V φ : E m → ℝ}
    (hV : ContDiff ℝ 1 V) (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {K : Set (E m)} (hK : IsCompact K) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ x ∈ K, ∀ y ∈ K,
      |Submission.Lib.EntropyRemainder.gaussianDensity y * Real.exp (V (gradient φ y)) -
        Submission.Lib.EntropyRemainder.gaussianDensity x * Real.exp (V (gradient φ x))| ≤
          C * ‖y - x‖ ^ α := by
  apply brenier_smooth_composition_compact_holder hm hV.continuous hφ hlaw
    (F := fun z => Submission.Lib.EntropyRemainder.gaussianDensity z.1 * Real.exp (V z.2))
    (K := K) _ hK
  exact (Submission.Lib.EntropyRemainder.gaussianDensity_contDiff.comp contDiff_fst).mul
    (hV.comp contDiff_snd).exp

end Submission.Obl.Entropy__smooth_gaussian_transport
