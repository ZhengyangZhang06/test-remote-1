import Submission.Lib.GaussianTransport.GaussianSlope

open Set Filter
open scoped Topology

namespace Submission.Obl.Entropy__hazard_secant_surplus

open Submission.Lib.GaussianTransport

noncomputable def varianceDefect (c a : ℝ) : ℝ :=
  1 - gaussianHazard a * gaussianGap a - c * gaussianGap a ^ 2

noncomputable def varianceTilt (c a : ℝ) : ℝ :=
  varianceDefect c a * Real.exp (-a ^ 2 / 2 - (2 + c) * Real.log (gaussianHazard a))

lemma hasDerivAt_varianceTilt (c a : ℝ) :
    HasDerivAt (varianceTilt c)
      (Real.exp (-a ^ 2 / 2 - (2 + c) * Real.log (gaussianHazard a)) * gaussianGap a *
        (c - 1 + c * (1 + c) * gaussianGap a ^ 2)) a := by
  have hd := (((hasDerivAt_gaussianHazard a).mul (hasDerivAt_gaussianGap a)).const_sub 1).sub
    (((hasDerivAt_gaussianGap a).pow 2).const_mul c)
  have hw := (((((hasDerivAt_id a).pow 2).neg).div_const 2).sub
    (((hasDerivAt_gaussianHazard a).log (ne_of_gt (gaussianHazard_pos a))).const_mul (2 + c))).exp
  convert! hd.mul hw using 1
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Pi.neg_apply, id_eq]
  unfold gaussianGap
  field_simp [ne_of_gt (gaussianHazard_pos a)]
  ring

lemma tendsto_gaussianGap_atTop : Tendsto gaussianGap atTop (𝓝 0) := by
  apply squeeze_zero (fun a => (gaussianGap_pos a).le)
    (fun a => ?_) (tendsto_inv_atTop_zero.comp tendsto_gaussianHazard_atTop)
  change gaussianGap a ≤ (gaussianHazard a)⁻¹
  rw [← one_div, le_div_iff₀ (gaussianHazard_pos a)]
  nlinarith [one_sub_hazard_mul_gap_pos a]

lemma tendsto_varianceTilt_atTop (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (varianceTilt c) atTop (𝓝 0) := by
  have ht : Tendsto (fun a => (1 + c) * gaussianGap a ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_gaussianGap_atTop.pow 2).const_mul (1 + c)
  apply squeeze_zero_norm' _ ht
  filter_upwards [tendsto_gaussianHazard_atTop.eventually_ge_atTop 1] with a ha
  have he : Real.exp (-a ^ 2 / 2 - (2 + c) * Real.log (gaussianHazard a)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have := Real.log_nonneg ha
    nlinarith [sq_nonneg a, mul_nonneg (show 0 ≤ 2 + c by linarith) this]
  have hd : |varianceDefect c a| ≤ (1 + c) * gaussianGap a ^ 2 := by
    apply abs_le.mpr
    have h1 := one_sub_hazard_mul_gap_pos a
    have h2 := one_sub_hazard_mul_gap_le_gap_sq a
    unfold varianceDefect
    constructor <;> nlinarith [sq_nonneg (gaussianGap a), mul_nonneg hc (sq_nonneg (gaussianGap a))]
  unfold varianceTilt
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left he (abs_nonneg _)).trans (by simpa using hd)

/-- A variance lower bound at one parameter propagates to all larger parameters. -/
lemma varianceDefect_nonneg_of_le {c a s : ℝ} (hc : 0 ≤ c)
    (ha : 0 ≤ varianceDefect c a) (has : a ≤ s) : 0 ≤ varianceDefect c s := by
  have hsource : Antitone (fun x => c - 1 + c * (1 + c) * gaussianGap x ^ 2) := by
    intro x y hxy
    have hd := antitone_gaussianGap hxy
    have hsq : gaussianGap y ^ 2 ≤ gaussianGap x ^ 2 :=
      pow_le_pow_left₀ (gaussianGap_pos y).le hd 2
    change c - 1 + c * (1 + c) * gaussianGap y ^ 2 ≤
      c - 1 + c * (1 + c) * gaussianGap x ^ 2
    exact add_le_add_right (mul_le_mul_of_nonneg_left hsq
      (mul_nonneg hc (by linarith))) (c - 1)
  have hcont : Continuous (varianceTilt c) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_varianceTilt c x).continuousAt
  have htilt : 0 ≤ varianceTilt c s := by
    by_cases hs : 0 ≤ c - 1 + c * (1 + c) * gaussianGap s ^ 2
    · have hm : MonotoneOn (varianceTilt c) (Icc a s) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont.continuousOn
        · exact fun x _ => (hasDerivAt_varianceTilt c x).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [(hasDerivAt_varianceTilt c x).deriv]
          have hxs : x ≤ s := (interior_subset hx).2
          exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (gaussianGap_pos x).le)
            (hs.trans (hsource hxs))
      exact (mul_nonneg ha (Real.exp_pos _).le).trans (hm ⟨le_rfl, has⟩ ⟨has, le_rfl⟩ has)
    · have hm : AntitoneOn (varianceTilt c) (Ici s) := by
        apply antitoneOn_of_deriv_nonpos (convex_Ici _) hcont.continuousOn
        · exact fun x _ => (hasDerivAt_varianceTilt c x).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [(hasDerivAt_varianceTilt c x).deriv]
          exact mul_nonpos_of_nonneg_of_nonpos
            (mul_nonneg (Real.exp_pos _).le (gaussianGap_pos x).le)
            ((hsource (interior_subset hx)).trans (le_of_not_ge hs))
      exact le_of_tendsto (tendsto_varianceTilt_atTop c hc)
        (by filter_upwards [eventually_ge_atTop s] with x hx; exact hm self_mem_Ici hx hx)
  exact (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).mp htilt

end Submission.Obl.Entropy__hazard_secant_surplus
