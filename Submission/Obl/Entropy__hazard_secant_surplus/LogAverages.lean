import Submission.Obl.Entropy__hazard_secant_surplus.Chebyshev
import Submission.Obl.Entropy__hazard_secant_surplus.Curvature

open MeasureTheory Set

namespace Submission.Obl.Entropy__hazard_secant_surplus

open Submission.Lib.GaussianTransport

lemma logarithmic_covariance {a b : ℝ} (hab : a < b) :
    (b - a) ^ 2 - (transportRatio b - transportRatio a) ^ 2 ≤
      (Real.log (gaussianHazard b) - Real.log (gaussianHazard a)) *
        (∫ s in Real.log (gaussianHazard a)..Real.log (gaussianHazard b), logM s) := by
  have h := interval_weighted_chebyshev (log_interval_lt hab).le
    (w := fun _ => 1) (f := fun s => logD s - logB s) (g := fun s => logD s + logB s)
    continuous_const.continuousOn (continuous_logD.sub continuous_logB).continuousOn
    (continuous_logD.add continuous_logB).continuousOn (fun _ _ => zero_le_one)
    (monotone_logD_sub_logB.monotoneOn _)
    ((monotone_logD_add_logB transportCurvature_nonneg).monotoneOn _)
  simp only [one_mul, ← logM_eq] at h
  rw [intervalIntegral.integral_sub (continuous_logD.intervalIntegrable _ _)
      (continuous_logB.intervalIntegrable _ _),
    intervalIntegral.integral_add (continuous_logD.intervalIntegrable _ _)
      (continuous_logB.intervalIntegrable _ _), integral_logD, integral_logB,
    intervalIntegral.integral_const, smul_eq_mul, mul_one] at h
  nlinarith

lemma ratio_increment_bounds {a b : ℝ} (hab : a < b) :
    0 ≤ transportRatio b - transportRatio a ∧
      transportRatio b - transportRatio a ≤ (b - a) / 2 := by
  have hlo := intervalIntegral.integral_nonneg (μ := volume) (log_interval_lt hab).le (fun s _ => logB_nonneg s)
  rw [integral_logB] at hlo
  have hhi := intervalIntegral.integral_mono_on (μ := volume) (log_interval_lt hab).le
    (continuous_logB.intervalIntegrable _ _) ((continuous_logD.const_mul (1 / 2 : ℝ)).intervalIntegrable _ _)
    (fun s _ => logB_le_half s)
  rw [intervalIntegral.integral_const_mul, integral_logB, integral_logD] at hhi
  exact ⟨hlo, by linarith⟩

lemma exponential_average_comparison (h : GrowthCertificate) {a b : ℝ} (hab : a < b) :
    (∫ s in Real.log (gaussianHazard a)..Real.log (gaussianHazard b),
        Real.exp ((1 + growthStep a) * s)) *
      (∫ s in Real.log (gaussianHazard a)..Real.log (gaussianHazard b), logM s) ≤
    (∫ s in Real.log (gaussianHazard a)..Real.log (gaussianHazard b), Real.exp (growthStep a * s)) *
      (∫ s in Real.log (gaussianHazard a)..Real.log (gaussianHazard b), Real.exp s * logM s) := by
  have hg : Continuous (fun s => logM s * Real.exp (-growthStep a * s)) :=
    continuous_logM.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hh := interval_weighted_chebyshev (log_interval_lt hab).le
    (w := fun s => Real.exp (growthStep a * s)) (f := Real.exp)
    (g := fun s => logM s * Real.exp (-growthStep a * s))
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    Real.continuous_exp.continuousOn hg.continuousOn (fun s _ => (Real.exp_pos _).le)
    (Real.exp_monotone.monotoneOn _)
    ((monotoneOn_tilted_logM h a).mono (fun s hs => hs.1))
  have h1 (s : ℝ) : Real.exp (growthStep a * s) * Real.exp s =
      Real.exp ((1 + growthStep a) * s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 (s : ℝ) : Real.exp (growthStep a * s) *
      (logM s * Real.exp (-growthStep a * s)) = logM s := by
    rw [mul_left_comm, ← Real.exp_add]
    simp only [neg_mul, add_neg_cancel, Real.exp_zero, mul_one]
  have h3 (s : ℝ) : Real.exp (growthStep a * s) *
      (Real.exp s * (logM s * Real.exp (-growthStep a * s))) = Real.exp s * logM s := by
    rw [mul_left_comm, h2]
  simpa only [h1, h2, h3] using hh

end Submission.Obl.Entropy__hazard_secant_surplus
