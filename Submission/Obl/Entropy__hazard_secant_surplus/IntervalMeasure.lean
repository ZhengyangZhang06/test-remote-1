import Submission.Obl.Entropy__hazard_secant_surplus.HyperbolicBridge

open MeasureTheory Set

namespace Submission.Obl.Entropy__hazard_secant_surplus

noncomputable def intervalProbability (u v : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Icc u v)

lemma intervalProbability_isProbability {u v : ℝ} (huv : u < v) :
    IsProbabilityMeasure (intervalProbability u v) :=
  ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    (by rw [Real.volume_Icc]; exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr huv)))
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)

lemma ae_intervalProbability_mem (u v : ℝ) :
    ∀ᵐ s ∂intervalProbability u v, s ∈ Icc u v :=
  ProbabilityTheory.ae_cond_mem measurableSet_Icc

lemma integral_intervalProbability (f : ℝ → ℝ) {u v : ℝ} (huv : u ≤ v) :
    (∫ s, f s ∂intervalProbability u v) = (∫ s in u..v, f s) / (v - u) := by
  rw [intervalProbability, ProbabilityTheory.cond, integral_smul_measure,
    Real.volume_Icc, ENNReal.toReal_inv, ENNReal.toReal_ofReal (sub_nonneg.mpr huv),
    smul_eq_mul, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huv]
  ring

lemma integrable_intervalProbability {f : ℝ → ℝ} {u v : ℝ} (huv : u < v)
    (hf : ContinuousOn f (Icc u v)) : Integrable f (intervalProbability u v) := by
  apply hf.integrableOn_Icc.smul_measure
  rw [Real.volume_Icc, ENNReal.inv_ne_top]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr huv))

open Submission.Lib.GaussianTransport

lemma log_interval_lt {a b : ℝ} (hab : a < b) :
    Real.log (gaussianHazard a) < Real.log (gaussianHazard b) :=
  Real.log_lt_log (gaussianHazard_pos a) (strictMono_gaussianHazard hab)

lemma logD_average {a b : ℝ} (hab : a ≤ b) :
    (∫ s, logD s ∂intervalProbability (Real.log (gaussianHazard a)) (Real.log (gaussianHazard b))) =
      (b - a) / (Real.log (gaussianHazard b) - Real.log (gaussianHazard a)) := by
  rw [integral_intervalProbability logD
    (Real.log_le_log (gaussianHazard_pos a) (strictMono_gaussianHazard.monotone hab)), integral_logD]

lemma logB_average {a b : ℝ} (hab : a ≤ b) :
    (∫ s, logB s ∂intervalProbability (Real.log (gaussianHazard a)) (Real.log (gaussianHazard b))) =
      (transportRatio b - transportRatio a) /
        (Real.log (gaussianHazard b) - Real.log (gaussianHazard a)) := by
  rw [integral_intervalProbability logB
    (Real.log_le_log (gaussianHazard_pos a) (strictMono_gaussianHazard.monotone hab)), integral_logB]

lemma arithmeticMean_integral {a b : ℝ} (hab : a < b) :
    arithmeticMean a b =
      (∫ s in Real.log (gaussianHazard a)..Real.log (gaussianHazard b), Real.exp s * logM s) /
        (gaussianHazard b - gaussianHazard a) := by
  rw [integral_exp_logM]
  simp only [arithmeticMean, if_neg (ne_of_lt hab)]
  convert (neg_div_neg_eq
    (gaussianHazard a * transportRatio a ^ 2 - gaussianHazard b * transportRatio b ^ 2)
    (gaussianHazard a - gaussianHazard b)).symm using 1 <;> congr 1 <;> ring

end Submission.Obl.Entropy__hazard_secant_surplus
