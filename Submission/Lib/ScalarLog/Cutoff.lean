/-
Adapted from: here:root
Original scalar logarithmic estimates by session x0023, following Section 4 of the supplied paper.
-/

import Submission.Lib.ScalarLog.SquareRoot
import Submission.Lib.EntropyTools.Remainder

open Submission.Lib.EntropyTools

namespace Submission.Lib.ScalarLog

/-- The two elementary logarithmic estimates combined with the paper's cutoff. -/
theorem logCost_rho_le_cutoff {s lam : ℝ} (hs : 0 < s) (hlam : 0 ≤ lam)
    (hrel : (3 / 40 : ℝ) * lam = 1 / s - 37 / 40) :
    (3 / 40) * logCost s / (3 / 20 + 1813 / 4000 * s) ≤ (86 / 125 : ℝ) * rigidityCutoff lam := by
  have hfirst := logCost_rho_le hs
  by_cases hzero : lam = 0
  · rw [rigidityCutoff, if_pos hzero]
    exact hfirst.trans (by norm_num)
  · have hlpos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hzero)
    have hsqrt := Real.sqrt_pos.mpr hlpos
    have hsecond := (le_div_iff₀ hsqrt).mpr (logCost_rho_mul_sqrt_le hs hlam hrel)
    rw [rigidityCutoff, if_neg hzero, mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 86 / 125)]
    apply le_min
    · exact hfirst.trans (by norm_num)
    · refine hsecond.trans ?_
      calc
        (22 / 25 : ℝ) / Real.sqrt lam ≤ ((86 / 125) * (32 / 25)) / Real.sqrt lam :=
          div_le_div_of_nonneg_right (by norm_num) hsqrt.le
        _ = (86 / 125) * (32 / (25 * Real.sqrt lam)) := by ring

/-- The supporting-plane scale for a nonnegative first-chaos eigenvalue. -/
noncomputable def dualScale (lam : ℝ) : ℝ := 40 / (37 + 3 * lam)

lemma dualScale_pos {lam : ℝ} (hlam : 0 ≤ lam) : 0 < dualScale lam := by
  unfold dualScale
  positivity

lemma dualScale_relation {lam : ℝ} (hlam : 0 ≤ lam) :
    (3 / 40 : ℝ) * lam = 1 / dualScale lam - 37 / 40 := by
  have hd : 37 + 3 * lam ≠ 0 := by positivity
  dsimp [dualScale]
  field_simp
  ring

/-- The logarithmic cost consumes at most `.688` of the retained rigidity weight. -/
theorem dual_log_le_weight {lam : ℝ} (hlam : 0 ≤ lam) :
    dualScale lam - 1 - Real.log (dualScale lam) ≤ (86 / 125 : ℝ) * rigidityWeight lam := by
  let s := dualScale lam
  have hs : 0 < s := dualScale_pos hlam
  by_cases hs1 : s = 1
  · change s - 1 - Real.log s ≤ _
    rw [hs1, Real.log_one]
    norm_num only
    exact mul_nonneg (by norm_num) (rigidityWeight_nonneg hlam)
  let H : ℝ := 3 * (lam - 1) ^ 2 / (37 + 3 * lam)
  let rho : ℝ := 3 / 20 + 49 / 100 * (37 / (37 + 3 * lam))
  have hd : 0 < 37 + 3 * lam := by positivity
  have hH0 : 0 ≤ H := by dsimp [H]; positivity
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hrhoeq : rho = 3 / 20 + 1813 / 4000 * s := by
    dsimp [rho, s, dualScale]
    ring
  have hH : H = (1 - s) ^ 2 / ((3 / 40) * s) := by
    dsimp [H, s, dualScale]
    field_simp
    ring
  have heq : H * (3 / 40) * logCost s = s - 1 - Real.log s := by
    rw [hH, logCost_eq hs hs1]
    field_simp
  have hcut := logCost_rho_le_cutoff hs hlam (dualScale_relation hlam)
  rw [← hrhoeq] at hcut
  have hcancel : H * rho * ((3 / 40) * logCost s / rho) = H * (3 / 40) * logCost s := by
    field_simp
  change s - 1 - Real.log s ≤ _
  calc
    s - 1 - Real.log s = H * rho * ((3 / 40) * logCost s / rho) := (hcancel.trans heq).symm
    _ ≤ H * rho * ((86 / 125) * rigidityCutoff lam) :=
      mul_le_mul_of_nonneg_left hcut (mul_nonneg hH0 hrho.le)
    _ = (86 / 125) * rigidityWeight lam := by
      change H * rho * ((86 / 125) * rigidityCutoff lam) =
        (86 / 125) * (H * rho * rigidityCutoff lam)
      ring

end Submission.Lib.ScalarLog
