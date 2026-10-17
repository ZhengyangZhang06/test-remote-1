/-
Adapted from: here:root
Original Gaussian-coordinate and secant-estimate proofs by session x0014.
-/

import Submission.Lib.GaussianCurvature.LogHazardCoordinates

open MeasureTheory Set

namespace Submission.Lib.GaussianCurvature.SecantBounds

open Submission.Lib.GaussianTransport LogHazardCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A derivative bounded relative to `d=(log q)'` is Lipschitz in logarithmic hazard. -/
theorem norm_sub_le_log_distance {a b C : ℝ} {g g' : ℝ → E}
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x)
    (hbound : ∀ x ∈ Icc a b, ‖g' x‖ ≤ C * gaussianGap x)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖g y - g x‖ ≤ C * |logHazard y - logHazard x| := by
  have hinv {t : ℝ} (ht : t ∈ Icc (logHazard a) (logHazard b)) :
      inverseLogHazard t ∈ Icc a b := by
    constructor
    · apply strictMono_logHazard.le_iff_le.mp
      rw [logHazard_inverseLogHazard]
      exact ht.1
    · apply strictMono_logHazard.le_iff_le.mp
      rw [logHazard_inverseLogHazard]
      exact ht.2
  have hder (t : ℝ) (ht : t ∈ Icc (logHazard a) (logHazard b)) :
      HasDerivAt (g ∘ inverseLogHazard)
        (logHazardWeight t • g' (inverseLogHazard t)) t :=
    (hg _ (hinv ht)).scomp t (hasDerivAt_inverseLogHazard t)
  have hnorm (t : ℝ) (ht : t ∈ Icc (logHazard a) (logHazard b)) :
      ‖logHazardWeight t • g' (inverseLogHazard t)‖ ≤ C := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (logHazardWeight_pos t)]
    calc
      _ ≤ logHazardWeight t * (C * gaussianGap (inverseLogHazard t)) :=
        mul_le_mul_of_nonneg_left (hbound _ (hinv ht)) (logHazardWeight_pos t).le
      _ = C := by unfold logHazardWeight; field_simp [(gaussianGap_pos _).ne']
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hder t ht).hasDerivWithinAt) hnorm (convex_Icc _ _)
    (show logHazard x ∈ Icc (logHazard a) (logHazard b) from
      ⟨strictMono_logHazard.monotone hx.1, strictMono_logHazard.monotone hx.2⟩)
    (show logHazard y ∈ Icc (logHazard a) (logHazard b) from
      ⟨strictMono_logHazard.monotone hy.1, strictMono_logHazard.monotone hy.2⟩)
  simpa only [Function.comp_apply, inverseLogHazard_logHazard, Real.norm_eq_abs] using h

variable [CompleteSpace E]

/-- Averaging the logarithmic distance controls the norm of an endpoint increment. -/
theorem norm_average_sub_endpoint_le {a b c C : ℝ} {g g' : ℝ → E} (hab : a < b) (hc : c ∈ Icc a b)
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x)
    (hbound : ∀ x ∈ Icc a b, ‖g' x‖ ≤ C * gaussianGap x) :
    ‖(b - a)⁻¹ • (∫ x in a..b, g x) - g c‖ ≤
      C / (b - a) * ∫ x in a..b, |logHazard x - logHazard c| := by
  have hcont : ContinuousOn g (Icc a b) :=
    fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable g volume a b := hcont.intervalIntegrable_of_Icc hab.le
  have hlog : Continuous (fun x => |logHazard x - logHazard c|) :=
    ((continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_logHazard x).continuousAt)).sub
      continuous_const).abs
  have hb : 0 < b - a := sub_pos.mpr hab
  have heq : (b - a)⁻¹ • (∫ x in a..b, g x) - g c =
      (b - a)⁻¹ • ∫ x in a..b, g x - g c := by
    rw [intervalIntegral.integral_sub hi (intervalIntegrable_const),
      intervalIntegral.integral_const, smul_sub, smul_smul, inv_mul_cancel₀ hb.ne', one_smul]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb)]
  have hint : ‖∫ x in a..b, g x - g c‖ ≤
      ∫ x in a..b, C * (|logHazard x - logHazard c|) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab.le
      (Filter.Eventually.of_forall (fun x hx => ?_)) ((continuous_const.mul hlog).intervalIntegrable a b)
    have h := norm_sub_le_log_distance hg hbound hc ⟨hx.1.le, hx.2⟩
    simpa only [Pi.mul_apply] using h
  have hmul := mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hb.le)
  rw [intervalIntegral.integral_const_mul] at hmul
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

theorem norm_average_sub_left_le {a b C : ℝ} {g g' : ℝ → E} (hab : a < b)
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x)
    (hbound : ∀ x ∈ Icc a b, ‖g' x‖ ≤ C * gaussianGap x) :
    ‖(b - a)⁻¹ • (∫ x in a..b, g x) - g a‖ ≤
      C / (b - a) * ∫ x in a..b, logHazard x - logHazard a := by
  have h := norm_average_sub_endpoint_le hab (left_mem_Icc.mpr hab.le) hg hbound
  have heq : (∫ x in a..b, |logHazard x - logHazard a|) =
      ∫ x in a..b, logHazard x - logHazard a := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab.le] at hx
    exact abs_of_nonneg (sub_nonneg.mpr (strictMono_logHazard.monotone hx.1))
  rwa [heq] at h

theorem norm_average_sub_right_le {a b C : ℝ} {g g' : ℝ → E} (hab : a < b)
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x)
    (hbound : ∀ x ∈ Icc a b, ‖g' x‖ ≤ C * gaussianGap x) :
    ‖(b - a)⁻¹ • (∫ x in a..b, g x) - g b‖ ≤
      C / (b - a) * ∫ x in a..b, logHazard b - logHazard x := by
  have h := norm_average_sub_endpoint_le hab (right_mem_Icc.mpr hab.le) hg hbound
  have heq : (∫ x in a..b, |logHazard x - logHazard b|) =
      ∫ x in a..b, logHazard b - logHazard x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab.le] at hx
    change |logHazard x - logHazard b| = logHazard b - logHazard x
    rw [abs_of_nonpos (sub_nonpos.mpr (strictMono_logHazard.monotone hx.2))]
    ring
  rwa [heq] at h

/-- The derivative average is the secant slope, including for vector-valued functions. -/
theorem norm_secant_sub_left_le {a b C : ℝ} {f g g' : ℝ → E} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x)
    (hbound : ∀ x ∈ Icc a b, ‖g' x‖ ≤ C * gaussianGap x) :
    ‖(b - a)⁻¹ • (f b - f a) - g a‖ ≤
      C / (b - a) * ∫ x in a..b, logHazard x - logHazard a := by
  have h := norm_average_sub_left_le hab hg hbound
  have hcont : ContinuousOn g (Icc a b) :=
    fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hf x (by simpa only [uIcc_of_le hab.le] using hx))
    (hcont.intervalIntegrable_of_Icc hab.le)
  rwa [hint] at h

theorem norm_secant_sub_right_le {a b C : ℝ} {f g g' : ℝ → E} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x)
    (hbound : ∀ x ∈ Icc a b, ‖g' x‖ ≤ C * gaussianGap x) :
    ‖(b - a)⁻¹ • (f b - f a) - g b‖ ≤
      C / (b - a) * ∫ x in a..b, logHazard b - logHazard x := by
  have h := norm_average_sub_right_le hab hg hbound
  have hcont : ContinuousOn g (Icc a b) :=
    fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hf x (by simpa only [uIcc_of_le hab.le] using hx))
    (hcont.intervalIntegrable_of_Icc hab.le)
  rwa [hint] at h

end Submission.Lib.GaussianCurvature.SecantBounds
