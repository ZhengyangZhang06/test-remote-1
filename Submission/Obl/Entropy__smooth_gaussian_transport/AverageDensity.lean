import Submission.Obl.Entropy__smooth_gaussian_transport.DeterminantConcavity
import Submission.Obl.Entropy__smooth_gaussian_transport.JacobianLowerBound
import Submission.Obl.Entropy__smooth_gaussian_transport.SymmetricAverage

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def symmetricDensity {m : ℕ} (V u : E m → ℝ) (h x : E m) : ℝ :=
  Submission.Lib.EntropyRemainder.gaussianDensity x *
    Real.exp (-‖h‖ ^ 2 / 2 + (V (gradient u (x + h)) + V (gradient u (x - h))) / 2)

theorem symmetricDensity_pos {m : ℕ} (V u : E m → ℝ) (h x : E m) :
    0 < symmetricDensity V u h x :=
  mul_pos (Submission.Lib.EntropyRemainder.gaussianDensity_pos x) (Real.exp_pos _)

theorem symmetricDensity_continuous {m : ℕ} {V u : E m → ℝ}
    (hV : Continuous V) (hu : ContDiff ℝ 1 u) (h : E m) :
    Continuous (symmetricDensity V u h) := by
  have hg := continuous_gradient_of_contDiff_one hu
  have hsum : Continuous (fun x =>
      (V (gradient u (x + h)) + V (gradient u (x - h))) / 2) :=
    (((hV.comp hg).comp (continuous_id.add continuous_const)).add
      ((hV.comp hg).comp (continuous_id.sub continuous_const))).div_const 2
  exact Submission.Lib.EntropyRemainder.gaussianDensity_continuous.mul
    (Real.continuous_exp.comp (continuous_const.add hsum))

theorem log_gaussianDensity_midpoint {m : ℕ} (x h : E m) :
    (Real.log (Submission.Lib.EntropyRemainder.gaussianDensity (x + h)) +
      Real.log (Submission.Lib.EntropyRemainder.gaussianDensity (x - h))) / 2 =
      Real.log (Submission.Lib.EntropyRemainder.gaussianDensity x) - ‖h‖ ^ 2 / 2 := by
  have hc : ((Real.sqrt (2 * Real.pi))⁻¹ ^ m : ℝ) ≠ 0 := by positivity
  simp only [Submission.Lib.EntropyRemainder.gaussianDensity,
    Real.log_mul hc (Real.exp_ne_zero _), Real.log_exp]
  nlinarith [norm_add_sq_real x h, norm_sub_sq_real x h]

/-- An averaged potential has at least the geometric mean of the two
translated Jacobian densities. This only uses almost-everywhere Hessians. -/
theorem brenier_ae_symmetricDensity_le_jacobian {m : ℕ} (hm : 1 ≤ m) {V φ : E m → ℝ}
    (hV : Continuous V) (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) (h : E m) :
    ∀ᵐ x ∂volume, symmetricDensity V φ h x ≤
      |(fderiv ℝ (gradient (symmetricAverage φ h)) x).det| := by
  have hAE := brenier_ae_positive_hessian hm hV hφ hlaw
  have hplus := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae hAE
  have hminus := (measurePreserving_sub_right volume h).quasiMeasurePreserving.ae hAE
  have hdφ := (brenier_contDiff_one hm hV hφ hlaw).1.differentiable_one
  filter_upwards [hplus, hminus] with x hp hn
  let A := fderiv ℝ (gradient φ) (x + h)
  let B := fderiv ℝ (gradient φ) (x - h)
  have hderiv : HasFDerivAt (gradient (symmetricAverage φ h))
      ((1 / 2 : ℝ) • (A + B)) x := by
    have he : gradient (symmetricAverage φ h) = fun y =>
        (1 / 2 : ℝ) • (gradient φ (y + h) + gradient φ (y - h)) :=
      funext (gradient_symmetricAverage hdφ h)
    rw [he]
    exact (((hasFDerivAt_comp_add_right h).mpr hp.1.hasFDerivAt).add
      ((hasFDerivAt_comp_sub h).mpr hn.1.hasFDerivAt)).const_smul (1 / 2 : ℝ)
  have hlog := log_det_operator_midpoint_concave hp.2.1 hn.2.1
  have heq : (Real.log A.det + Real.log B.det) / 2 =
      Real.log (symmetricDensity V φ h x) := by
    change (Real.log ((fderiv ℝ (gradient φ) (x + h)).det) +
      Real.log ((fderiv ℝ (gradient φ) (x - h)).det)) / 2 = _
    rw [hp.2.2, hn.2.2]
    simp only [symmetricDensity,
      Real.log_mul (Submission.Lib.EntropyRemainder.gaussianDensity_pos _).ne'
        (Real.exp_ne_zero _), Real.log_exp]
    have he := log_gaussianDensity_midpoint x h
    linarith
  rw [← hderiv.fderiv] at hlog
  change (Real.log A.det + Real.log B.det) / 2 ≤ _ at hlog
  rw [heq] at hlog
  have hh := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (symmetricDensity_pos V φ h x)] at hh
  by_cases hz : (fderiv ℝ (gradient (symmetricAverage φ h)) x).det = 0
  · have hpos : (operatorMatrix ((1 / 2 : ℝ) • (A + B))).PosDef := by
      simpa only [operatorMatrix, ContinuousLinearMap.toLinearMap_smul,
        ContinuousLinearMap.toLinearMap_add, map_smul, map_add] using
        (hp.2.1.add hn.2.1).smul (by norm_num : (0 : ℝ) < 1 / 2)
    have hne : ((1 / 2 : ℝ) • (A + B)).det ≠ 0 := by
      simpa only [operatorMatrix_det] using hpos.det_pos.ne'
    exact False.elim (hne ((congrArg ContinuousLinearMap.det hderiv.fderiv).symm.trans hz))
  · simpa only [Real.exp_log_eq_abs hz] using hh

theorem brenier_symmetricDensity_measure_le {m : ℕ} (hm : 1 ≤ m) {V φ : E m → ℝ}
    (hV : Continuous V) (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) (h : E m) :
    volume.withDensity (fun x => ENNReal.ofReal (symmetricDensity V φ h x)) ≤
      alexandrovMeasure (symmetricAverage φ h) := by
  have hC1 := (brenier_contDiff_one hm hV hφ hlaw).1
  have hstrict := (brenier_strictConvexOn hm hV hφ hlaw).1
  have hdom : conjugateDomain φ = univ := by
    apply conjugateDomain_eq_univ_of_transport hφ (stdGaussian_absolutelyContinuous m)
    rw [hlaw]
    exact target_support hV
  exact density_measure_le_alexandrov_of_ae_le_jacobian
    (symmetricAverage_convex hφ h) (symmetricAverage_contDiff hC1 h)
    (symmetricAverage_conjugateDomain hφ hdom h)
    (gradient_injective_of_strictConvex (symmetricAverage_strictConvex hstrict h)
      (symmetricAverage_contDiff hC1 h).differentiable_one)
    (brenier_ae_symmetricDensity_le_jacobian hm hV hφ hlaw h)

end Submission.Obl.Entropy__smooth_gaussian_transport
