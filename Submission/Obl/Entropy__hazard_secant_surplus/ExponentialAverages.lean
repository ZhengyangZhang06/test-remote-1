import Submission.Obl.Entropy__hazard_secant_surplus.LogAverages
import Submission.Obl.Entropy__hazard_secant_surplus.Hyperbolic

open MeasureTheory Set

namespace Submission.Obl.Entropy__hazard_secant_surplus

lemma integral_exp_centered {u v c : ℝ} (huv : u < v) :
    (∫ s in u..v, Real.exp (c * s)) =
      (v - u) * Real.exp (c * ((u + v) / 2)) * sinhc (c * ((v - u) / 2)) := by
  by_cases hc : c = 0
  · subst c
    simp [sinhc, intervalIntegral.integral_const]
  have hd : (v - u) / 2 ≠ 0 := ne_of_gt (by linarith)
  rw [intervalIntegral.integral_comp_mul_left Real.exp hc, integral_exp, smul_eq_mul,
    sinhc, if_neg (mul_ne_zero hc hd), Real.sinh_eq]
  have hv : c * v = c * ((u + v) / 2) + c * ((v - u) / 2) := by ring
  have hu : c * u = c * ((u + v) / 2) + -(c * ((v - u) / 2)) := by ring
  rw [hv, hu, Real.exp_add, Real.exp_add]
  field_simp [hc, ne_of_gt (sub_pos.mpr huv)]

lemma integral_exp_mul_pos {u v : ℝ} (huv : u < v) (c : ℝ) :
    0 < ∫ s in u..v, Real.exp (c * s) := by
  apply intervalIntegral.integral_pos huv
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    (fun s _ => (Real.exp_pos _).le)
  exact ⟨u, left_mem_Icc.mpr huv.le, Real.exp_pos _⟩

lemma exponential_integral_ratio {u v m : ℝ} (huv : u < v) (hm : 0 ≤ m) :
    (v - u) * (∫ s in u..v, Real.exp ((1 + m) * s)) /
      ((∫ s in u..v, Real.exp s) * (∫ s in u..v, Real.exp (m * s))) =
    sinhc ((1 + m) * ((v - u) / 2)) /
      (sinhc ((v - u) / 2) * sinhc (m * ((v - u) / 2))) := by
  have he : (∫ s in u..v, Real.exp s) =
      (v - u) * Real.exp ((u + v) / 2) * sinhc ((v - u) / 2) := by
    simpa only [one_mul] using (integral_exp_centered (c := 1) huv)
  rw [integral_exp_centered huv, he, integral_exp_centered huv]
  rw [add_mul, one_mul, Real.exp_add]
  have hx : 0 < (v - u) / 2 := by linarith
  field_simp [ne_of_gt (sub_pos.mpr huv), Real.exp_ne_zero,
    ne_of_gt (sinhc_pos hx.le), ne_of_gt (sinhc_pos (mul_nonneg hm hx.le))]

open Submission.Lib.GaussianTransport

lemma arithmeticMean_ge_hyperbolic (h : GrowthCertificate) {a b : ℝ} (hab : a < b) :
    sinhc ((1 + growthStep a) * ((Real.log (gaussianHazard b) - Real.log (gaussianHazard a)) / 2)) /
      (sinhc ((Real.log (gaussianHazard b) - Real.log (gaussianHazard a)) / 2) *
        sinhc (growthStep a * ((Real.log (gaussianHazard b) - Real.log (gaussianHazard a)) / 2))) *
      ((∫ s in Real.log (gaussianHazard a)..Real.log (gaussianHazard b), logM s) /
        (Real.log (gaussianHazard b) - Real.log (gaussianHazard a))) ≤ arithmeticMean a b := by
  let u := Real.log (gaussianHazard a)
  let v := Real.log (gaussianHazard b)
  let m := growthStep a
  have huv : u < v := log_interval_lt hab
  have hE : 0 < ∫ s in u..v, Real.exp s := by
    simpa only [one_mul] using integral_exp_mul_pos huv 1
  have hEm := integral_exp_mul_pos huv m
  have hδ : v - u ≠ 0 := ne_of_gt (sub_pos.mpr huv)
  have he : (∫ s in u..v, Real.exp s) = gaussianHazard b - gaussianHazard a := by
    rw [integral_exp, Real.exp_log (gaussianHazard_pos b), Real.exp_log (gaussianHazard_pos a)]
  rw [arithmeticMean_integral hab, ← he]
  change _ ≤ (∫ s in u..v, Real.exp s * logM s) / (∫ s in u..v, Real.exp s)
  apply (le_div_iff₀ hE).mpr
  calc
    _ = ((∫ s in u..v, Real.exp ((1 + m) * s)) * (∫ s in u..v, logM s)) /
        (∫ s in u..v, Real.exp (m * s)) := by
      rw [← exponential_integral_ratio huv (growthStep_nonneg a)]
      dsimp only [u, v, m] at *
      field_simp [hδ, ne_of_gt hE, ne_of_gt hEm]
    _ ≤ ∫ s in u..v, Real.exp s * logM s := by
      apply (div_le_iff₀ hEm).mpr
      simpa only [mul_comm] using exponential_average_comparison h hab

end Submission.Obl.Entropy__hazard_secant_surplus
