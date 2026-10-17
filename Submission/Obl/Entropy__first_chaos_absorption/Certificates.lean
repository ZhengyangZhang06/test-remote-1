import Submission.Obl.Entropy__first_chaos_absorption.TailCertificate
import Submission.Obl.Entropy__first_chaos_absorption.PositiveCertificate
import Submission.Obl.Entropy__absorption_p_lower_bounds
import Submission.Obl.Entropy__absorption_h_square_bound

namespace Submission.Obl.Entropy__first_chaos_absorption

open Submission.Lib.GaussianTransport

lemma pValue_lower_bounds (a : ℝ) :
    (a ≤ 0 → 1 / (7 + a^2) ≤ pValue a) ∧
    (0 ≤ a → (1/4 : ℝ) ≤ pValue a) ∧
    (4 ≤ a → (23/50 : ℝ) ≤ pValue a) := by
  by_cases ha : a ≤ -6
  · exact ⟨fun _ => (negative_tail_certificates ha).1, fun ha0 => by linarith,
      fun ha4 => by linarith⟩
  by_cases ha10 : 10 ≤ a
  · have hp := (positive_tail_certificates ha10).1
    exact ⟨fun ha0 => by linarith, fun _ => by linarith, fun _ => hp⟩
  have hp := Submission.Entropy.absorption_p_lower_bounds a (by linarith) (by linarith)
  change (a ≤ 0 → 1 / (7 + a^2) ≤
      deriv (fun z => transportRatio z * (1 + deriv transportRatio z)) a -
        (deriv transportRatio a)^2 - (40/3)*(deriv (deriv transportRatio) a)^2) ∧
    (0 ≤ a → (1/4 : ℝ) ≤
      deriv (fun z => transportRatio z * (1 + deriv transportRatio z)) a -
        (deriv transportRatio a)^2 - (40/3)*(deriv (deriv transportRatio) a)^2) ∧
    (4 ≤ a → (23/50 : ℝ) ≤
      deriv (fun z => transportRatio z * (1 + deriv transportRatio z)) a -
        (deriv transportRatio a)^2 - (40/3)*(deriv (deriv transportRatio) a)^2) at hp
  rw [deriv_transportRatio_eq, deriv_transportSlope_eq] at hp
  simpa only [← pValue_eq_deriv] using hp

lemma pValue_pos (a : ℝ) : 0 < pValue a := by
  rcases le_total a 0 with ha | ha
  · exact lt_of_lt_of_le (by positivity) ((pValue_lower_bounds a).1 ha)
  · exact lt_of_lt_of_le (by norm_num) ((pValue_lower_bounds a).2.1 ha)

lemma hValue_sq_le (a : ℝ) : (hValue a)^2 ≤ (67/100 : ℝ)^2 * pValue a := by
  by_cases ha : a ≤ -6
  · exact (negative_tail_certificates ha).2
  by_cases ha10 : 10 ≤ a
  · exact (positive_tail_certificates ha10).2
  have hh := Submission.Entropy.absorption_h_square_bound a (by linarith) (by linarith)
  change (transportRatio a * (1 + deriv transportRatio a) - (3/2)*transportRatio a -
      (80/3)*(deriv transportRatio a - 7/25)*deriv (deriv transportRatio) a)^2 ≤
    (67/100 : ℝ)^2 *
      (deriv (fun z => transportRatio z * (1 + deriv transportRatio z)) a -
        (deriv transportRatio a)^2 - (40/3)*(deriv (deriv transportRatio) a)^2) at hh
  rw [deriv_transportRatio_eq, deriv_transportSlope_eq] at hh
  simpa only [← pValue_eq_deriv, ← hValue_eq] using hh

lemma yCostValue_le (a : ℝ) : yCostValue a ≤ 111/1000 := by
  have hb0 := (transportSlope_pos a).le
  have hb1 := (transportSlope_lt_half a).le
  have hb : (transportSlope a - 7/25)^2 ≤ (7/25 : ℝ)^2 := by nlinarith
  have hh : (hValue a)^2 / pValue a ≤ (67/100 : ℝ)^2 :=
    (div_le_iff₀ (pValue_pos a)).2 (hValue_sq_le a)
  unfold yCostValue
  rw [mul_div_assoc]
  nlinarith

end Submission.Obl.Entropy__first_chaos_absorption
