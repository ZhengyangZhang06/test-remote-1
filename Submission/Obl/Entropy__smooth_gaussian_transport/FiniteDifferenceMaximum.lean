import Submission.Obl.Entropy__smooth_gaussian_transport.AverageDensity
import Submission.Obl.Entropy__smooth_gaussian_transport.DensityTouching
import Submission.Obl.Entropy__smooth_gaussian_transport.HessianBounds

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem gradient_eq_at_localMax_difference {m : ℕ} {u v : E m → ℝ} {x : E m}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x)
    (hmax : IsLocalMax (fun y => v y - u y) x) : gradient v x = gradient u x := by
  have he := hmax.hasFDerivAt_eq_zero (hv.hasFDerivAt.sub hu.hasFDerivAt)
  apply (InnerProductSpace.toDual ℝ (E m)).injective
  simpa only [toDual_gradient] using sub_eq_zero.mp he

/-- Uniform target convexity controls the two translated gradients at every
local maximum of the potential's centered second difference. -/
theorem brenier_gradient_difference_at_localMax {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    (h x : E m) (hmax : IsLocalMax (fun y => symmetricAverage φ h y - φ y) x) :
    a * ‖gradient φ (x + h) - gradient φ (x - h)‖ ^ 2 ≤ 4 * ‖h‖ ^ 2 := by
  have hC1 := (brenier_contDiff_one hm hV.continuous hφ hlaw).1
  have hstrict := (brenier_strictConvexOn hm hV.continuous hφ hlaw).1
  have hdom : conjugateDomain φ = univ := by
    apply conjugateDomain_eq_univ_of_transport hφ (stdGaussian_absolutelyContinuous m)
    rw [hlaw]
    exact target_support hV.continuous
  have hdensity := density_le_at_localMax_difference hm hφ
    (symmetricAverage_strictConvex hstrict h) hdom (symmetricAverage_conjugateDomain hφ hdom h)
    (brenier_alexandrov_continuous_density hm hV.continuous hφ hlaw)
    (symmetricDensity_continuous hV.continuous hC1 h)
    (brenier_alexandrov_density hV.continuous hφ hlaw)
    (brenier_symmetricDensity_measure_le hm hV.continuous hφ hlaw h)
    (mul_pos (Submission.Lib.EntropyRemainder.gaussianDensity_pos x) (Real.exp_pos _)).le hmax
  change Submission.Lib.EntropyRemainder.gaussianDensity x *
      Real.exp (-‖h‖ ^ 2 / 2 + (V (gradient φ (x + h)) + V (gradient φ (x - h))) / 2) ≤
    Submission.Lib.EntropyRemainder.gaussianDensity x * Real.exp (V (gradient φ x)) at hdensity
  have hpotential := Real.exp_le_exp.mp
    ((mul_le_mul_iff_right₀ (Submission.Lib.EntropyRemainder.gaussianDensity_pos x)).mp hdensity)
  have hgrad := gradient_eq_at_localMax_difference (hC1.differentiable_one x)
    ((symmetricAverage_contDiff hC1 h).differentiable_one x) hmax
  rw [gradient_symmetricAverage hC1.differentiable_one] at hgrad
  have hstrong := strongConvexOn_of_hessian_lower hV hH
  have hj := hstrong.2 (mem_univ (gradient φ (x + h))) (mem_univ (gradient φ (x - h)))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  rw [← smul_add, hgrad] at hj
  simp only [smul_eq_mul] at hj
  linarith

theorem symmetricAverage_sub_le_gradient_difference {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hd : Differentiable ℝ u) (h x : E m) :
    symmetricAverage u h x - u x ≤
      ‖gradient u (x + h) - gradient u (x - h)‖ * ‖h‖ / 2 := by
  have hp := convex_gradient_support hu (hd (x + h)) x
  have hn := convex_gradient_support hu (hd (x - h)) x
  have he₁ : x - (x + h) = -h := by abel
  have he₂ : x - (x - h) = h := by abel
  rw [he₁, inner_neg_right] at hp
  rw [he₂] at hn
  have hc := real_inner_le_norm (gradient u (x + h) - gradient u (x - h)) h
  rw [inner_sub_left] at hc
  dsimp only [symmetricAverage]
  linarith

/-- The finite-difference bound at a local maximum needs no classical second
derivative at the maximum point. -/
theorem brenier_second_difference_at_localMax {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    (h x : E m) (hmax : IsLocalMax (fun y => symmetricAverage φ h y - φ y) x) :
    symmetricAverage φ h x - φ x ≤ ‖h‖ ^ 2 / Real.sqrt a := by
  have hd := (brenier_contDiff_one hm hV.continuous hφ hlaw).1.differentiable_one
  have h₁ := brenier_gradient_difference_at_localMax hm hV hH hφ hlaw h x hmax
  have h₂ := symmetricAverage_sub_le_gradient_difference hφ hd h x
  have hs : Real.sqrt a * ‖gradient φ (x + h) - gradient φ (x - h)‖ ≤ 2 * ‖h‖ := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt ha.le]
    nlinarith
  have h₃ := mul_le_mul_of_nonneg_left h₂ (Real.sqrt_nonneg a)
  have h₄ := mul_le_mul_of_nonneg_right hs (norm_nonneg h)
  apply (le_div_iff₀ (Real.sqrt_pos.mpr ha)).mpr
  nlinarith

/-- A compact-region maximum principle for centered second differences. The
boundary bound is explicit; no assertion about behavior at infinity is used. -/
theorem brenier_second_difference_maximum_principle {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    (h : E m) {K : Set (E m)} (hK : IsCompact K) {C : ℝ}
    (hC : ‖h‖ ^ 2 / Real.sqrt a ≤ C)
    (hboundary : ∀ x ∈ frontier K, symmetricAverage φ h x - φ x ≤ C) :
    ∀ x ∈ K, symmetricAverage φ h x - φ x ≤ C := by
  intro x hx
  have hC1 := (brenier_contDiff_one hm hV.continuous hφ hlaw).1
  have hc := (symmetricAverage_contDiff hC1 h).continuous.sub hC1.continuous
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ hc.continuousOn
  by_cases hzint : z ∈ interior K
  · have hl : IsLocalMax (fun y => symmetricAverage φ h y - φ y) z := by
      filter_upwards [mem_interior_iff_mem_nhds.mp hzint] with y hy
      exact hmax hy
    exact (hmax hx).trans ((brenier_second_difference_at_localMax hm hV ha hH hφ hlaw h z hl).trans hC)
  · exact (hmax hx).trans (hboundary z ⟨subset_closure hz, hzint⟩)

end Submission.Obl.Entropy__smooth_gaussian_transport
