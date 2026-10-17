import Submission.Obl.Entropy__smooth_gaussian_transport.HessianBounds
import Submission.Obl.Entropy__smooth_gaussian_transport.DifferentiableTransport

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem integrable_exp_neg_norm_sq {m : ℕ} {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : E m => Real.exp (-a * ‖x‖ ^ 2)) volume := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (b := (a : ℂ)) (by simpa using ha) (0 : ℂ) (0 : E m)
  convert! h.norm using 1
  ext x
  simp only [zero_mul, add_zero, Complex.norm_exp, ← Complex.ofReal_pow,
    ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem target_integrable_exp_norm_sq {m : ℕ} {V : E m → ℝ} {a : ℝ}
    (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v) :
    Integrable (fun x => Real.exp (a / 8 * ‖x‖ ^ 2))
      (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) := by
  obtain ⟨C, hC⟩ := exists_quadratic_minorant hV ha hH
  have hρ : Continuous (fun x => Real.exp (-V x)) := Real.continuous_exp.comp hV.continuous.neg
  apply (integrable_withDensity_iff_integrable_smul₀'
    hρ.measurable.ennreal_ofReal.aemeasurable
    (by simp)).2
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  apply ((integrable_exp_neg_norm_sq (m := m) (show 0 < a / 8 by positivity)).const_mul
    (Real.exp C)).mono' ((hρ.mul (by fun_prop)).aestronglyMeasurable)
  filter_upwards [] with x
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)),
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [hC x]

theorem brenier_integrable_exp_gradient_sq {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    Integrable (fun x => Submission.Lib.EntropyRemainder.gaussianDensity x *
      Real.exp (a / 8 * ‖gradient φ x‖ ^ 2)) volume := by
  have htarget := target_integrable_exp_norm_sq hV ha hH
  rw [← hlaw] at htarget
  have hg := continuous_gradient_of_contDiff_one (brenier_contDiff_one hm hV.continuous hφ hlaw).1
  have hi := htarget.comp_measurable hg.measurable
  exact Submission.Lib.EntropyRemainder.gaussian_integrable_iff.mp hi

end Submission.Obl.Entropy__smooth_gaussian_transport
