import Submission.Obl.Entropy__smooth_gaussian_transport.PenalizedMaximum
import Submission.Obl.Entropy__smooth_gaussian_transport.PenalizedEstimate

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- A global quadratic bound for centered second differences of the Brenier
potential. The penalized maxima are attained because the gradient has linear
growth and the potential is superlinear. -/
theorem brenier_global_second_difference {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) (h x : E m) :
    symmetricAverage φ h x - φ x ≤ ‖h‖ ^ 2 / Real.sqrt a := by
  have hC1 := (brenier_contDiff_one hm hV.continuous hφ hlaw).1
  have hgrowth := brenier_gradient_linear_growth hm hV ha hH hφ hlaw
  have hdom : conjugateDomain φ = univ := by
    apply conjugateDomain_eq_univ_of_transport hφ (stdGaussian_absolutelyContinuous m)
    rw [hlaw]
    exact target_support hV.continuous
  obtain ⟨p, hp⟩ := exists_minimizer_of_hessian_lower hV ha hH
  obtain ⟨M, hM⟩ := bounded_conjugate_values hdom p
  have hbound (c : ℝ) (hc : 1 < c) : symmetricAverage φ h x - φ x ≤
      ‖h‖ * Real.sqrt (‖h‖ ^ 2 + 2 * (m : ℝ) * Real.log c) / Real.sqrt a +
        (c - 1) * (M + φ x - inner ℝ p x) := by
    obtain ⟨z, hz⟩ := exists_max_penalized_symmetricAverage hφ hC1 hdom hgrowth p h hc
    have hl : IsLocalMax (fun y => symmetricAverage φ h y - scaledTilt φ p c y) z :=
      Eventually.of_forall hz
    have hest := brenier_second_difference_at_penalized_max hm hV ha hH hφ hlaw hp hc h z hl
    have hlow := mul_le_mul_of_nonneg_left (hM (mem_range_self z)) (sub_pos.mpr hc).le
    have hcmp := hz x
    dsimp only [scaledTilt] at hcmp
    nlinarith only [hcmp, hest, hlow]
  have hc : Tendsto (fun c : ℝ => c) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) := nhdsWithin_le_nhds
  have hlog : Tendsto (fun c : ℝ => Real.log c) (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [Real.log_one, Function.comp_def] using (Real.continuousAt_log one_ne_zero).tendsto.comp hc
  have hs : Tendsto (fun c : ℝ => ‖h‖ ^ 2 + 2 * (m : ℝ) * Real.log c)
      (𝓝[>] (1 : ℝ)) (𝓝 (‖h‖ ^ 2)) := by
    simpa only [mul_zero, add_zero] using tendsto_const_nhds.add (hlog.const_mul (2 * (m : ℝ)))
  have hroot : Tendsto (fun c : ℝ => Real.sqrt (‖h‖ ^ 2 + 2 * (m : ℝ) * Real.log c))
      (𝓝[>] (1 : ℝ)) (𝓝 ‖h‖) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Function.comp_def] using (Real.continuous_sqrt.tendsto _).comp hs
  have ht := ((hroot.const_mul ‖h‖).div_const (Real.sqrt a)).add
    ((hc.sub_const 1).mul_const (M + φ x - inner ℝ p x))
  have hcpos : ∀ᶠ c : ℝ in 𝓝[>] (1 : ℝ), 1 < c := self_mem_nhdsWithin
  have he : ∀ᶠ c : ℝ in 𝓝[>] (1 : ℝ), symmetricAverage φ h x - φ x ≤
      ‖h‖ * Real.sqrt (‖h‖ ^ 2 + 2 * (m : ℝ) * Real.log c) / Real.sqrt a +
        (c - 1) * (M + φ x - inner ℝ p x) :=
    hcpos.mono (fun c hc => hbound c hc)
  simpa only [sub_self, zero_mul, add_zero, ← sq] using ge_of_tendsto ht he

end Submission.Obl.Entropy__smooth_gaussian_transport
