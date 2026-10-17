import Submission.Obl.Entropy__smooth_gaussian_transport.ScaledTilt

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem brenier_gradient_difference_at_penalized_max {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {p : E m} (hp : ∀ y, V p ≤ V y) {c : ℝ} (hc : 1 < c) (h x : E m)
    (hmax : IsLocalMax (fun y => symmetricAverage φ h y - scaledTilt φ p c y) x) :
    a * ‖gradient φ (x + h) - gradient φ (x - h)‖ ^ 2 ≤
      4 * ‖h‖ ^ 2 + 8 * (m : ℝ) * Real.log c := by
  have hcpos : 0 < c := zero_lt_one.trans hc
  have hC1 := (brenier_contDiff_one hm hV.continuous hφ hlaw).1
  have hstrict := (brenier_strictConvexOn hm hV.continuous hφ hlaw).1
  have hdom : conjugateDomain φ = univ := by
    apply conjugateDomain_eq_univ_of_transport hφ (stdGaussian_absolutelyContinuous m)
    rw [hlaw]
    exact target_support hV.continuous
  have hcont := brenier_alexandrov_continuous_density hm hV.continuous hφ hlaw
  have hdensity := density_le_at_localMax_difference hm (scaledTilt_convex hφ p hcpos.le)
    (symmetricAverage_strictConvex hstrict h) (scaledTilt_conjugateDomain hdom p hcpos)
    (symmetricAverage_conjugateDomain hφ hdom h) (continuous_const.mul hcont)
    (symmetricDensity_continuous hV.continuous hC1 h)
    (scaledTilt_alexandrov_density hC1.continuous hdom
      (brenier_alexandrov_density hV.continuous hφ hlaw) p hcpos)
    (brenier_symmetricDensity_measure_le hm hV.continuous hφ hlaw h)
    (mul_pos (pow_pos hcpos m) (mul_pos
      (Submission.Lib.EntropyRemainder.gaussianDensity_pos x) (Real.exp_pos _))).le hmax
  change Submission.Lib.EntropyRemainder.gaussianDensity x *
      Real.exp (-‖h‖ ^ 2 / 2 + (V (gradient φ (x + h)) + V (gradient φ (x - h))) / 2) ≤
    c ^ m * (Submission.Lib.EntropyRemainder.gaussianDensity x * Real.exp (V (gradient φ x))) at hdensity
  have hexp : Real.exp (-‖h‖ ^ 2 / 2 +
      (V (gradient φ (x + h)) + V (gradient φ (x - h))) / 2) ≤
      c ^ m * Real.exp (V (gradient φ x)) := by
    apply (mul_le_mul_iff_right₀ (Submission.Lib.EntropyRemainder.gaussianDensity_pos x)).mp
    simpa only [mul_left_comm, mul_assoc] using hdensity
  have hpotential := Real.log_le_log (Real.exp_pos _) hexp
  rw [Real.log_exp, Real.log_mul (pow_pos hcpos m).ne' (Real.exp_ne_zero _),
    Real.log_pow, Real.log_exp] at hpotential
  have hgrad := gradient_eq_at_localMax_difference
    ((scaledTilt_contDiff hC1 p c).differentiable_one x)
    ((symmetricAverage_contDiff hC1 h).differentiable_one x) hmax
  rw [gradient_symmetricAverage hC1.differentiable_one,
    gradient_scaledTilt hC1.differentiable_one] at hgrad
  have hstrong := strongConvexOn_of_hessian_lower hV hH
  have hVc := convex_of_hessian_nonneg hV (fun x v => (by positivity : 0 ≤ a * ‖v‖ ^ 2).trans (hH x v))
  have hr := convex_value_le_radial_dilation hVc hp hc.le (gradient φ x)
  have hj := hstrong.2 (mem_univ (gradient φ (x + h))) (mem_univ (gradient φ (x - h)))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  rw [← smul_add, hgrad] at hj
  simp only [smul_eq_mul] at hj
  linarith

theorem brenier_second_difference_at_penalized_max {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {p : E m} (hp : ∀ y, V p ≤ V y) {c : ℝ} (hc : 1 < c) (h x : E m)
    (hmax : IsLocalMax (fun y => symmetricAverage φ h y - scaledTilt φ p c y) x) :
    symmetricAverage φ h x - φ x ≤
      ‖h‖ * Real.sqrt (‖h‖ ^ 2 + 2 * (m : ℝ) * Real.log c) / Real.sqrt a := by
  have hd := (brenier_contDiff_one hm hV.continuous hφ hlaw).1.differentiable_one
  have h₁ := brenier_gradient_difference_at_penalized_max hm hV ha hH hφ hlaw hp hc h x hmax
  have h₂ := symmetricAverage_sub_le_gradient_difference hφ hd h x
  have hS : 0 ≤ ‖h‖ ^ 2 + 2 * (m : ℝ) * Real.log c := by
    positivity [Real.log_nonneg hc.le]
  have hs : Real.sqrt a * ‖gradient φ (x + h) - gradient φ (x - h)‖ ≤
      2 * Real.sqrt (‖h‖ ^ 2 + 2 * (m : ℝ) * Real.log c) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt ha.le, mul_pow, Real.sq_sqrt hS]
    nlinarith
  have h₃ := mul_le_mul_of_nonneg_left h₂ (Real.sqrt_nonneg a)
  have h₄ := mul_le_mul_of_nonneg_right hs (norm_nonneg h)
  apply (le_div_iff₀ (Real.sqrt_pos.mpr ha)).mpr
  nlinarith

end Submission.Obl.Entropy__smooth_gaussian_transport
