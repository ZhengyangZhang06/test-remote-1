import Submission.Lib.GaussianTransport.GaussianSlope
import Submission.Lib.GaussianTransport.GaussianInverse

open MeasureTheory Set Filter
open scoped Topology

namespace Submission.Obl.Entropy__hazard_secant_surplus

open Submission.Lib.GaussianTransport

noncomputable def dividedDifference (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  if a = b then deriv f a else (f a - f b) / (a - b)

noncomputable def arithmeticMean (a b : ℝ) : ℝ :=
  if a = b then transportRatio a ^ 2 +
    2 * transportRatio a * deriv transportRatio a / gaussianGap a
  else (gaussianHazard a * transportRatio a ^ 2 -
    gaussianHazard b * transportRatio b ^ 2) / (gaussianHazard a - gaussianHazard b)

noncomputable def growthStep (a : ℝ) : ℝ :=
  if a < -3 then 0 else if a < -2 then 19 / 100 else if a < -1 then 38 / 100 else 68 / 100

noncomputable def separation (a b : ℝ) : ℝ :=
  Real.log (gaussianHazard a) - Real.log (gaussianHazard b)

noncomputable def surplus (a b : ℝ) : ℝ :=
  (1 + growthStep (min a b)) / 16 *
    (1 + separation a b ^ 2 / 30 + separation a b ^ 4 / 1680) * separation a b ^ 2

noncomputable def scalarM (a : ℝ) : ℝ :=
  (1 - transportSlope a ^ 2) / gaussianGap a ^ 2

lemma dividedDifference_symm (f : ℝ → ℝ) (a b : ℝ) :
    dividedDifference f a b = dividedDifference f b a := by
  by_cases h : a = b
  · subst b; rfl
  · simp only [dividedDifference, if_neg h, if_neg (Ne.symm h)]
    simpa only [neg_sub] using (neg_div_neg_eq (f a - f b) (a - b)).symm

lemma arithmeticMean_symm (a b : ℝ) : arithmeticMean a b = arithmeticMean b a := by
  by_cases h : a = b
  · subst b; rfl
  · simp only [arithmeticMean, if_neg h, if_neg (Ne.symm h)]
    convert (neg_div_neg_eq
      (gaussianHazard a * transportRatio a ^ 2 - gaussianHazard b * transportRatio b ^ 2)
      (gaussianHazard a - gaussianHazard b)).symm using 1 <;> congr 1 <;> ring

lemma surplus_symm (a b : ℝ) : surplus a b = surplus b a := by
  unfold surplus separation
  rw [min_comm a b]
  have h : Real.log (gaussianHazard a) - Real.log (gaussianHazard b) =
      -(Real.log (gaussianHazard b) - Real.log (gaussianHazard a)) := by ring
  rw [h]
  ring

lemma scalarM_pos (a : ℝ) : 0 < scalarM a := by
  have hb := transportSlope_pos a
  have hb' := transportSlope_lt_half a
  apply div_pos _ (sq_pos_of_pos (gaussianGap_pos a))
  nlinarith

lemma arithmeticMean_self (a : ℝ) : arithmeticMean a a = scalarM a := by
  simp only [arithmeticMean, ite_true, (hasDerivAt_transportRatio a).deriv]
  unfold scalarM transportSlope
  field_simp [ne_of_gt (gaussianGap_pos a)]
  ring

lemma diagonal_identity (a : ℝ) :
    1 - dividedDifference transportRatio a a ^ 2 + surplus a a =
      dividedDifference gaussianHazard a a ^ 2 * arithmeticMean a a /
        (gaussianHazard a * gaussianHazard a) := by
  simp only [dividedDifference, ite_true, surplus, separation, sub_self,
    zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0), mul_zero, add_zero]
  rw [arithmeticMean_self, (hasDerivAt_transportRatio a).deriv,
    (hasDerivAt_gaussianHazard a).deriv]
  change 1 - transportSlope a ^ 2 =
    (gaussianHazard a * gaussianGap a) ^ 2 * scalarM a /
      (gaussianHazard a * gaussianHazard a)
  unfold scalarM
  field_simp [ne_of_gt (gaussianHazard_pos a), ne_of_gt (gaussianGap_pos a)]

lemma continuous_transportRatio : Continuous transportRatio :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_transportRatio x).continuousAt

lemma continuous_transportSlope : Continuous transportSlope :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_transportSlope x).continuousAt

lemma continuous_scalarM : Continuous scalarM :=
  (continuous_const.sub (continuous_transportSlope.pow 2)).div
    ((show Continuous gaussianGap from continuous_iff_continuousAt.mpr
      fun x => (hasDerivAt_gaussianGap x).continuousAt).pow 2)
    (fun x => pow_ne_zero _ (ne_of_gt (gaussianGap_pos x)))

lemma scalarM_eq_product (a : ℝ) :
    scalarM a = transportRatio a * ((1 + transportSlope a) / gaussianGap a) := by
  unfold scalarM transportSlope
  field_simp [ne_of_gt (gaussianGap_pos a)]
  ring

lemma hasDerivAt_weighted_square (a : ℝ) :
    HasDerivAt (fun x => gaussianHazard x * transportRatio x ^ 2)
      (scalarM a * (gaussianHazard a * gaussianGap a)) a := by
  convert! (hasDerivAt_gaussianHazard a).mul ((hasDerivAt_transportRatio a).pow 2) using 1
  change scalarM a * (gaussianHazard a * gaussianGap a) =
    gaussianHazard a * gaussianGap a * transportRatio a ^ 2 +
      gaussianHazard a * (2 * transportRatio a ^ 1 * transportSlope a)
  unfold scalarM transportSlope
  field_simp [ne_of_gt (gaussianGap_pos a)]
  ring

lemma growthStep_nonneg (a : ℝ) : 0 ≤ growthStep a := by
  unfold growthStep
  split_ifs <;> norm_num

lemma growthStep_le_one (a : ℝ) : growthStep a ≤ 1 := by
  unfold growthStep
  split_ifs <;> norm_num

lemma monotone_growthStep : Monotone growthStep := by
  intro a b hab
  unfold growthStep
  split_ifs <;> norm_num <;> linarith

end Submission.Obl.Entropy__hazard_secant_surplus
