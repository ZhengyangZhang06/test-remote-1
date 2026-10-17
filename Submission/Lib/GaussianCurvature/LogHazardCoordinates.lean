/-
Adapted from: here:root
Original Gaussian-coordinate and secant-estimate proofs by session x0014.
-/

import Submission.Lib.GaussianCurvature.MeanDistance
import Submission.Lib.GaussianTransport.GaussianInverse
import Submission.Lib.GaussianTransport.GaussianConvexity

open MeasureTheory Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Lib.GaussianCurvature.LogHazardCoordinates

open Submission.Lib.GaussianTransport

noncomputable def logHazard (a : ℝ) : ℝ := Real.log (gaussianHazard a)
noncomputable def inverseLogHazard (t : ℝ) : ℝ := inverseGaussianHazard (Real.exp t)
noncomputable def logHazardWeight (t : ℝ) : ℝ := 1 / gaussianGap (inverseLogHazard t)

theorem hasDerivAt_logHazard (a : ℝ) : HasDerivAt logHazard (gaussianGap a) a := by
  have h := (hasDerivAt_gaussianHazard a).log (gaussianHazard_pos a).ne'
  change HasDerivAt logHazard _ a at h
  apply h.congr_deriv
  dsimp [gaussianGap]
  field_simp [(gaussianHazard_pos a).ne']

theorem strictMono_logHazard : StrictMono logHazard :=
  strictMono_of_hasDerivAt_pos hasDerivAt_logHazard gaussianGap_pos

theorem inverseLogHazard_logHazard (a : ℝ) : inverseLogHazard (logHazard a) = a := by
  unfold inverseLogHazard logHazard
  rw [Real.exp_log (gaussianHazard_pos a), inverseGaussianHazard_gaussianHazard]

theorem logHazard_inverseLogHazard (t : ℝ) : logHazard (inverseLogHazard t) = t := by
  unfold inverseLogHazard logHazard
  rw [gaussianHazard_inverseGaussianHazard (Real.exp_pos t), Real.log_exp]

theorem logHazardWeight_pos (t : ℝ) : 0 < logHazardWeight t :=
  one_div_pos.mpr (gaussianGap_pos _)

theorem hasDerivAt_inverseLogHazard (t : ℝ) :
    HasDerivAt inverseLogHazard (logHazardWeight t) t := by
  have h := (hasStrictDerivAt_inverseGaussianHazard (Real.exp_pos t)).hasDerivAt.comp t
    (Real.hasDerivAt_exp t)
  change HasDerivAt inverseLogHazard _ t at h
  apply h.congr_deriv
  rw [(hasDerivAt_gaussianHazard _).deriv]
  change (gaussianHazard (inverseLogHazard t) * gaussianGap (inverseLogHazard t))⁻¹ *
    Real.exp t = _
  have hq : gaussianHazard (inverseLogHazard t) = Real.exp t :=
    gaussianHazard_inverseGaussianHazard (Real.exp_pos t)
  rw [hq]
  unfold logHazardWeight
  field_simp [(gaussianGap_pos _).ne', (Real.exp_pos t).ne']

theorem hasDerivAt_logHazardWeight (t : ℝ) :
    HasDerivAt logHazardWeight
      ((1 - gaussianHazard (inverseLogHazard t) * gaussianGap (inverseLogHazard t)) /
        gaussianGap (inverseLogHazard t) ^ 3) t := by
  have h := (hasDerivAt_const t (1 : ℝ)).div
    ((hasDerivAt_gaussianGap _).comp t (hasDerivAt_inverseLogHazard t)) (gaussianGap_pos _).ne'
  change HasDerivAt logHazardWeight _ t at h
  apply h.congr_deriv
  dsimp [logHazardWeight]
  field_simp [(gaussianGap_pos _).ne']
  ring

theorem continuous_logHazardWeight : Continuous logHazardWeight :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_logHazardWeight t).continuousAt)

theorem strictMono_logHazardWeight : StrictMono logHazardWeight := by
  apply strictMono_of_hasDerivAt_pos hasDerivAt_logHazardWeight
  intro t
  exact div_pos (one_sub_hazard_mul_gap_pos _) (pow_pos (gaussianGap_pos _) 3)

theorem hasDerivAt_tiltedWeight (t : ℝ) :
    HasDerivAt (fun t => logHazardWeight t / Real.exp t)
      ((1 - gaussianHazard (inverseLogHazard t) * gaussianGap (inverseLogHazard t) -
        gaussianGap (inverseLogHazard t) ^ 2) /
          (gaussianGap (inverseLogHazard t) ^ 3 * Real.exp t)) t := by
  have h := (hasDerivAt_logHazardWeight t).div (Real.hasDerivAt_exp t) (Real.exp_pos t).ne'
  apply h.congr_deriv
  dsimp [logHazardWeight]
  field_simp [(gaussianGap_pos _).ne', (Real.exp_pos t).ne']

theorem strictAnti_tiltedWeight : StrictAnti (fun t => logHazardWeight t / Real.exp t) := by
  apply strictAnti_of_hasDerivAt_neg hasDerivAt_tiltedWeight
  intro t
  exact div_neg_of_neg_of_pos (sub_neg.mpr (one_sub_hazard_mul_gap_lt_gap_sq _))
    (mul_pos (pow_pos (gaussianGap_pos _) 3) (Real.exp_pos t))

theorem antitone_shift_tiltedWeight (c : ℝ) :
    Antitone (fun t => logHazardWeight (c + t) / Real.exp t) := by
  intro x y hxy
  have h := strictAnti_tiltedWeight.antitone (show c + x ≤ c + y by linarith)
  have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos c).le
  simpa only [Real.exp_add, ← mul_div_assoc,
    mul_div_mul_left _ _ (Real.exp_pos c).ne'] using hmul

theorem integral_shift_weight (c d : ℝ) :
    (∫ x in 0..d, logHazardWeight (c + x)) = inverseLogHazard (c + d) - inverseLogHazard c := by
  have hd (x : ℝ) : HasDerivAt (fun x => inverseLogHazard (c + x))
      (logHazardWeight (c + x)) x := by
    convert! (hasDerivAt_inverseLogHazard (c + x)).comp x
      ((hasDerivAt_id x).const_add c) using 1 <;> simp
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((continuous_logHazardWeight.comp (continuous_const.add continuous_id)).intervalIntegrable 0 d)

/-- The exact mean-distance estimate in the original Gaussian parameter. -/
theorem gaussian_mean_distance_bounds {a b : ℝ} (hab : a < b) :
    let d := logHazard b - logHazard a
    let u := (∫ x in a..b, logHazard x - logHazard a) / (d * (b - a))
    1 / 2 ≤ u ∧ u ≤ 1 / 2 + d / 12 ∧
      u ^ 2 + (1 - u) ^ 2 ≤ (1 + d ^ 2 / 36) / 2 := by
  let d := logHazard b - logHazard a
  have hd : 0 < d := sub_pos.mpr (strictMono_logHazard hab)
  have hc : logHazard a + d = logHazard b := by dsimp [d]; ring
  have hcont : Continuous (fun x => logHazardWeight (logHazard a + x)) :=
    continuous_logHazardWeight.comp (continuous_const.add continuous_id)
  have hmass : (∫ x in Icc 0 d, logHazardWeight (logHazard a + x)) = b - a := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hd.le,
      integral_shift_weight, hc, inverseLogHazard_logHazard, inverseLogHazard_logHazard]
  have hmoment : (∫ x in Icc 0 d, x * logHazardWeight (logHazard a + x)) =
      ∫ x in a..b, logHazard x - logHazard a := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hd.le]
    have h := intervalIntegral.integral_comp_mul_deriv
      (a := 0) (b := d) (f := fun x => inverseLogHazard (logHazard a + x))
      (f' := fun x => logHazardWeight (logHazard a + x))
      (g := fun x => logHazard x - logHazard a)
      (fun x _ => by
        convert! (hasDerivAt_inverseLogHazard (logHazard a + x)).comp x
          ((hasDerivAt_id x).const_add (logHazard a)) using 1 <;> simp)
      hcont.continuousOn
      ((continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_logHazard x).continuousAt)).sub
        continuous_const)
    simpa only [Function.comp_apply, logHazard_inverseLogHazard,
      add_sub_cancel_left, add_zero, hc, inverseLogHazard_logHazard] using h
  have hm : MonotoneOn (fun x => logHazardWeight (logHazard a + x)) (Icc 0 d) := by
    intro x _ y _ hxy
    exact strictMono_logHazardWeight.monotone (by linarith)
  have ha := (antitone_shift_tiltedWeight (logHazard a)).antitoneOn (s := Icc 0 d)
  have h := MeanDistance.normalized_mean_distance_bounds hd hcont.continuousOn
    (show 0 < ∫ x in Icc 0 d, logHazardWeight (logHazard a + x) by rw [hmass]; linarith)
    hm ha
  dsimp only at h ⊢
  rw [hmass, hmoment] at h
  exact h

/-- The complementary normalized endpoint distance is nonnegative. -/
theorem gaussian_mean_distance_le_one {a b : ℝ} (hab : a < b) :
    (∫ x in a..b, logHazard x - logHazard a) /
      ((logHazard b - logHazard a) * (b - a)) ≤ 1 := by
  have hd := sub_pos.mpr (strictMono_logHazard hab)
  have hlog : Continuous (fun x => logHazard x - logHazard a) :=
    (continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_logHazard x).continuousAt)).sub
      continuous_const
  have h := intervalIntegral.integral_mono_on (μ := volume) hab.le (hlog.intervalIntegrable a b)
    (intervalIntegrable_const (c := logHazard b - logHazard a))
    (fun x hx => sub_le_sub_right (strictMono_logHazard.monotone hx.2) (logHazard a))
  rw [intervalIntegral.integral_const] at h
  simp only [smul_eq_mul] at h
  apply (div_le_iff₀ (mul_pos hd (sub_pos.mpr hab))).mpr
  nlinarith

end Submission.Lib.GaussianCurvature.LogHazardCoordinates
