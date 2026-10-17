import Submission.Obl.Entropy__hazard_secant_surplus.Growth

open MeasureTheory Set
open scoped Topology

namespace Submission.Obl.Entropy__hazard_secant_surplus

open Submission.Lib.GaussianTransport

noncomputable def logParameter (s : ℝ) : ℝ := inverseGaussianHazard (Real.exp s)
noncomputable def logD (s : ℝ) : ℝ := (gaussianGap (logParameter s))⁻¹
noncomputable def logB (s : ℝ) : ℝ := transportSlope (logParameter s) * logD s
noncomputable def logM (s : ℝ) : ℝ := scalarM (logParameter s)

lemma hazard_logParameter (s : ℝ) : gaussianHazard (logParameter s) = Real.exp s :=
  gaussianHazard_inverseGaussianHazard (Real.exp_pos s)

lemma logParameter_log_hazard (a : ℝ) : logParameter (Real.log (gaussianHazard a)) = a := by
  simp only [logParameter, Real.exp_log (gaussianHazard_pos a), inverseGaussianHazard_gaussianHazard]

lemma strictMono_logParameter : StrictMono logParameter := by
  intro s t hst
  exact strictMonoOn_inverseGaussianHazard (Real.exp_pos s) (Real.exp_pos t)
    (Real.exp_lt_exp.mpr hst)

lemma hasDerivAt_logParameter (s : ℝ) : HasDerivAt logParameter (logD s) s := by
  convert! (hasStrictDerivAt_inverseGaussianHazard (Real.exp_pos s)).hasDerivAt.comp s
    (Real.hasDerivAt_exp s) using 1
  rw [(hasDerivAt_gaussianHazard _).deriv]
  change logD s = (gaussianHazard (logParameter s) * gaussianGap (logParameter s))⁻¹ * Real.exp s
  rw [hazard_logParameter]
  unfold logD
  field_simp [ne_of_gt (Real.exp_pos s), ne_of_gt (gaussianGap_pos (logParameter s))]

lemma continuous_logParameter : Continuous logParameter :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_logParameter s).continuousAt

lemma continuous_logD : Continuous logD :=
  ((continuous_iff_continuousAt.mpr fun a => (hasDerivAt_gaussianGap a).continuousAt).comp
    continuous_logParameter).inv₀ (fun s => ne_of_gt (gaussianGap_pos (logParameter s)))

lemma continuous_logB : Continuous logB :=
  (continuous_transportSlope.comp continuous_logParameter).mul continuous_logD

lemma continuous_logM : Continuous logM := continuous_scalarM.comp continuous_logParameter

lemma logD_pos (s : ℝ) : 0 < logD s := inv_pos.mpr (gaussianGap_pos _)

lemma logM_pos (s : ℝ) : 0 < logM s := scalarM_pos _

lemma logB_nonneg (s : ℝ) : 0 ≤ logB s :=
  mul_nonneg (transportSlope_pos _).le (logD_pos s).le

lemma logB_le_half (s : ℝ) : logB s ≤ (1 / 2 : ℝ) * logD s :=
  mul_le_mul_of_nonneg_right (transportSlope_lt_half _).le (logD_pos s).le

lemma logD_sub_logB (s : ℝ) : logD s - logB s = transportRatio (logParameter s) := by
  unfold logB transportSlope logD
  field_simp [ne_of_gt (gaussianGap_pos (logParameter s))]
  ring

lemma logD_add_logB (s : ℝ) : logD s + logB s =
    (1 + transportSlope (logParameter s)) / gaussianGap (logParameter s) := by
  unfold logB logD
  ring

lemma logM_eq (s : ℝ) : logM s = (logD s - logB s) * (logD s + logB s) := by
  unfold logM scalarM logB logD
  ring

lemma monotone_logD_sub_logB : Monotone (fun s => logD s - logB s) := by
  simp_rw [logD_sub_logB]
  exact monotone_transportRatio.comp strictMono_logParameter.monotone

lemma monotone_logD_add_logB (hl : ∀ a, 0 ≤ transportCurvature a) :
    Monotone (fun s => logD s + logB s) := by
  simp_rw [logD_add_logB]
  exact (monotone_other_factor hl).comp strictMono_logParameter.monotone

lemma hasDerivAt_ratio_logParameter (s : ℝ) :
    HasDerivAt (fun t => transportRatio (logParameter t)) (logB s) s :=
  (hasDerivAt_transportRatio _).comp s (hasDerivAt_logParameter s)

lemma hasDerivAt_square_logParameter (s : ℝ) :
    HasDerivAt (fun t => gaussianHazard (logParameter t) * transportRatio (logParameter t) ^ 2)
      (Real.exp s * logM s) s := by
  convert! (hasDerivAt_weighted_square (logParameter s)).comp s (hasDerivAt_logParameter s) using 1
  rw [hazard_logParameter]
  unfold logM logD
  field_simp [ne_of_gt (gaussianGap_pos (logParameter s))]

lemma integral_logD (a b : ℝ) :
    (∫ s in Real.log (gaussianHazard a)..Real.log (gaussianHazard b), logD s) = b - a := by
  simpa only [logParameter_log_hazard] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_logParameter s)
      (continuous_logD.intervalIntegrable (Real.log (gaussianHazard a)) (Real.log (gaussianHazard b)))

lemma integral_logB (a b : ℝ) :
    (∫ s in Real.log (gaussianHazard a)..Real.log (gaussianHazard b), logB s) =
      transportRatio b - transportRatio a := by
  simpa only [logParameter_log_hazard] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_ratio_logParameter s)
      (continuous_logB.intervalIntegrable (Real.log (gaussianHazard a)) (Real.log (gaussianHazard b)))

lemma integral_exp_logM (a b : ℝ) :
    (∫ s in Real.log (gaussianHazard a)..Real.log (gaussianHazard b), Real.exp s * logM s) =
      gaussianHazard b * transportRatio b ^ 2 - gaussianHazard a * transportRatio a ^ 2 := by
  simpa only [logParameter_log_hazard] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_square_logParameter s)
      ((Real.continuous_exp.mul continuous_logM).intervalIntegrable
        (Real.log (gaussianHazard a)) (Real.log (gaussianHazard b)))

lemma hasDerivAt_logM (s : ℝ) :
    HasDerivAt logM (deriv scalarM (logParameter s) * logD s) s :=
  (hasDerivAt_scalarM _).differentiableAt.hasDerivAt.comp s (hasDerivAt_logParameter s)

lemma logM_growth (h : GrowthCertificate) (s : ℝ) :
    growthStep (logParameter s) * logM s ≤ deriv logM s := by
  rw [(hasDerivAt_logM s).deriv]
  have hh := mul_le_mul_of_nonneg_right (growth_inequality h (logParameter s)) (logD_pos s).le
  simpa only [logD, logM, mul_assoc, mul_inv_cancel₀ (ne_of_gt (gaussianGap_pos _)), mul_one] using hh

lemma monotoneOn_tilted_logM (h : GrowthCertificate) (a : ℝ) :
    MonotoneOn (fun s => logM s * Real.exp (-growthStep a * s))
      (Ici (Real.log (gaussianHazard a))) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
  · exact (continuous_logM.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn
  · intro s hs
    exact ((hasDerivAt_logM s).mul
      (((hasDerivAt_id s).const_mul (-growthStep a)).exp)).hasDerivWithinAt
  · intro s hs
    have ha : a ≤ logParameter s := by
      rw [← logParameter_log_hazard a]
      exact strictMono_logParameter.monotone (interior_subset hs)
    have hg := (mul_le_mul_of_nonneg_right (monotone_growthStep ha) (logM_pos s).le).trans
      (logM_growth h s)
    rw [(hasDerivAt_logM s).deriv] at hg
    simp only [id_eq, mul_one]
    nlinarith [mul_nonneg (sub_nonneg.mpr hg) (Real.exp_pos (-growthStep a * s)).le]

end Submission.Obl.Entropy__hazard_secant_surplus
