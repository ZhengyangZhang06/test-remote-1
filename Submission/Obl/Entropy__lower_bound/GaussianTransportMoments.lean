import Submission.Obl.Entropy__lower_bound.GaussianPushforward
import Submission.Obl.Entropy__affine_exponential_moments.Exponential

set_option backward.isDefEq.respectTransparency false

/-! Moments of the scalar transport, reusing the accepted exponential moment formulas. -/

open MeasureTheory ProbabilityTheory Set
open Submission.Obl.Entropy__affine_exponential_moments

namespace Submission.Obl.Entropy__lower_bound

private theorem expMeasure_one_eq :
    expMeasure 1 = volume.withDensity (fun x => ENNReal.ofReal (expDensity x)) := by
  change volume.withDensity (gammaPDF 1 1) = _
  apply congrArg (fun f : ℝ → ENNReal => volume.withDensity f)
  funext x
  simp [gammaPDF, gammaPDFReal, expDensity, indicator_apply]

private theorem measurable_expDensity_ofReal :
    Measurable (fun x => ENNReal.ofReal (expDensity x)) :=
  ((Real.continuous_exp.comp continuous_id.neg).measurable.indicator
    measurableSet_Ici).ennreal_ofReal

/-- The accepted exponential density moments also describe Mathlib's exponential measure. -/
theorem integral_pow_expMeasure (k : ℕ) :
    (∫ x : ℝ, x ^ k ∂expMeasure 1) = (k.factorial : ℝ) := by
  rw [expMeasure_one_eq, integral_withDensity_eq_integral_toReal_smul
    measurable_expDensity_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simpa only [ENNReal.toReal_ofReal (expDensity_nonneg _), smul_eq_mul] using
    integral_expDensity_pow k

/-- All polynomial moments of the exponential measure are integrable. -/
theorem integrable_pow_expMeasure (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (expMeasure 1) := by
  rw [expMeasure_one_eq, integrable_withDensity_iff_integrable_smul'
    measurable_expDensity_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simpa only [ENNReal.toReal_ofReal (expDensity_nonneg _), smul_eq_mul] using
    integrable_expDensity_pow k

/-- The scalar Gaussian transport has the factorial moments of an exponential variable. -/
theorem integral_exponentialTransport_pow (k : ℕ) :
    (∫ x, exponentialTransport x ^ k ∂gaussianReal 0 1) = (k.factorial : ℝ) := by
  calc
    _ = ∫ x : ℝ, x ^ k ∂expMeasure 1 :=
      hasLaw_exponentialTransport.integral_comp (by fun_prop)
    _ = _ := integral_pow_expMeasure k

/-- The transport has integrable powers of every natural order. -/
theorem integrable_exponentialTransport_pow (k : ℕ) :
    Integrable (fun x => exponentialTransport x ^ k) (gaussianReal 0 1) := by
  exact (hasLaw_exponentialTransport.measurePreserving
    contDiff_exponentialTransport.continuous.measurable).integrable_comp_of_integrable
      (integrable_pow_expMeasure k)

/-- The mean-one benchmark in Section 2.1. -/
theorem integral_exponentialTransport :
    (∫ x, exponentialTransport x ∂gaussianReal 0 1) = 1 := by
  simpa using integral_exponentialTransport_pow 1

/-- The centered second moment of the transport is one. -/
theorem integral_exponentialTransport_centered_sq :
    (∫ x, (exponentialTransport x - 1) ^ 2 ∂gaussianReal 0 1) = 1 := by
  have hi : Integrable exponentialTransport (gaussianReal 0 1) := by
    simpa using integrable_exponentialTransport_pow 1
  have hform : (fun x => (exponentialTransport x - 1) ^ 2) =
      (fun x => exponentialTransport x ^ 2 - 2 * exponentialTransport x + 1) := by
    funext x
    ring
  have hs : Integrable (fun x => exponentialTransport x ^ 2 - 2 * exponentialTransport x)
      (gaussianReal 0 1) := (integrable_exponentialTransport_pow 2).sub (hi.const_mul 2)
  rw [hform, integral_add hs (integrable_const 1),
    integral_sub (integrable_exponentialTransport_pow 2) (hi.const_mul 2),
    integral_const_mul, integral_exponentialTransport_pow, integral_exponentialTransport]
  norm_num

/-- The identity `q k = t` has Gaussian expectation one. -/
theorem integral_gaussianHazard_mul_transportRatio :
    (∫ x, gaussianHazard x * transportRatio x ∂gaussianReal 0 1) = 1 := by
  simp only [gaussianHazard_mul_transportRatio, integral_exponentialTransport]

end Submission.Obl.Entropy__lower_bound
