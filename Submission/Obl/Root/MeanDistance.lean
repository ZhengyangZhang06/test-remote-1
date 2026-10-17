import Mathlib

open MeasureTheory Set

namespace Submission.Obl.Root.MeanDistance

/-- A derivative proof of the hyperbolic bound in the mean-distance estimate. -/
theorem mul_cosh_le_sinh_cubic (x : ℝ) (hx : 0 ≤ x) :
    x * Real.cosh x ≤ (1 + x ^ 2 / 3) * Real.sinh x := by
  have hd1 (y : ℝ) : HasDerivAt (fun y => y * Real.cosh y - Real.sinh y)
      (y * Real.sinh y) y := by
    convert! ((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)).sub
      (Real.hasDerivAt_sinh y) using 1 <;> (dsimp; ring)
  have hm1 : Monotone (fun y => y * Real.cosh y - Real.sinh y) := by
    apply monotone_of_hasDerivAt_nonneg hd1
    intro y
    by_cases hy : 0 ≤ y
    · exact mul_nonneg hy (Real.sinh_nonneg_iff.mpr hy)
    · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hy)
        (Real.sinh_nonpos_iff.mpr (le_of_not_ge hy))
  have hd2 (y : ℝ) :
      HasDerivAt (fun y => (1 + y ^ 2 / 3) * Real.sinh y - y * Real.cosh y)
        (y / 3 * (y * Real.cosh y - Real.sinh y)) y := by
    convert! (((((hasDerivAt_id y).pow 2).div_const 3).const_add 1).mul
      (Real.hasDerivAt_sinh y)).sub ((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y))
        using 1 <;> (dsimp; ring)
  have hm2 : Monotone (fun y => (1 + y ^ 2 / 3) * Real.sinh y - y * Real.cosh y) := by
    apply monotone_of_hasDerivAt_nonneg hd2
    intro y
    by_cases hy : 0 ≤ y
    · have hh := hm1 hy
      simp only [zero_mul, Real.sinh_zero, sub_self] at hh
      exact mul_nonneg (div_nonneg hy (by norm_num)) hh
    · have hh := hm1 (le_of_not_ge hy)
      simp only [zero_mul, Real.sinh_zero, sub_self] at hh
      exact mul_nonneg_of_nonpos_of_nonpos (div_nonpos_of_nonpos_of_nonneg
        (le_of_not_ge hy) (by norm_num)) hh
  have h := hm2 hx
  simpa only [Real.sinh_zero, mul_zero, zero_mul, sub_self, sub_nonneg] using h

/-- The mean of the exponential density on `[0,d]` is at most `d/2+d²/12`. -/
theorem exponential_mean_le {d : ℝ} (hd : 0 < d) :
    d * Real.exp d / (Real.exp d - 1) - 1 ≤ d / 2 + d ^ 2 / 12 := by
  have he := Real.exp_pos (d / 2)
  have hdexp : Real.exp d = Real.exp (d / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hh := mul_cosh_le_sinh_cubic (d / 2) (by linarith)
  have h : d / 2 * (Real.exp d + 1) ≤
      (1 + d ^ 2 / 12) * (Real.exp d - 1) := by
    calc
      _ = (d / 2 * Real.cosh (d / 2)) * (2 * Real.exp (d / 2)) := by
        rw [hdexp, Real.cosh_eq, Real.exp_neg]
        field_simp [he.ne']
      _ ≤ ((1 + (d / 2) ^ 2 / 3) * Real.sinh (d / 2)) *
          (2 * Real.exp (d / 2)) := mul_le_mul_of_nonneg_right hh (by positivity)
      _ = _ := by
        rw [hdexp, Real.sinh_eq, Real.exp_neg]
        field_simp [he.ne']
        <;> ring
  have hden : 0 < Real.exp d - 1 := by linarith [Real.one_lt_exp_iff.mpr hd]
  rw [sub_le_iff_le_add, div_le_iff₀ hden]
  nlinarith

private theorem integral_sub_sub_add {μ : Measure ℝ} {f g h k : ℝ → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ)
    (hk : Integrable k μ) :
    (∫ x, f x - g x - h x + k x ∂μ) =
      (∫ x, f x ∂μ) - (∫ x, g x ∂μ) - (∫ x, h x ∂μ) + (∫ x, k x ∂μ) := by
  have h1 := integral_sub hf hg
  have h2 := integral_sub (hf.sub hg) hh
  have h3 := integral_add ((hf.sub hg).sub hh) hk
  simp only [Pi.sub_apply] at h1 h2 h3
  rw [h3, h2, h1]

/-- Comparing two weights by their likelihood ratio compares their means. -/
theorem weighted_mean_cross_le {μ : Measure ℝ} {w v : ℝ → ℝ}
    (hw : Integrable w μ) (hv : Integrable v μ)
    (hxw : Integrable (fun x => x * w x) μ)
    (hxv : Integrable (fun x => x * v x) μ)
    (hcross : ∀ᵐ y ∂μ, ∀ᵐ x ∂μ, (x - y) * (w x * v y - v x * w y) ≤ 0) :
    (∫ x, x * w x ∂μ) * (∫ x, v x ∂μ) ≤
      (∫ x, x * v x ∂μ) * (∫ x, w x ∂μ) := by
  have hp : ∀ᵐ y ∂μ,
      (∫ x, x * w x ∂μ) * v y - (∫ x, x * v x ∂μ) * w y -
        (∫ x, w x ∂μ) * (y * v y) + (∫ x, v x ∂μ) * (y * w y) ≤ 0 := by
    filter_upwards [hcross] with y hy
    have hn : ∫ x, (x * w x) * v y - (x * v x) * w y -
        w x * (y * v y) + v x * (y * w y) ∂μ ≤ 0 := by
      apply integral_nonpos_of_ae
      filter_upwards [hy] with x hx
      simp only [Pi.zero_apply]
      nlinarith only [hx]
    rw [integral_sub_sub_add (hxw.mul_const _) (hxv.mul_const _)
      (hw.mul_const _) (hv.mul_const _)] at hn
    simpa only [integral_mul_const] using hn
  have hn := integral_nonpos_of_ae hp
  rw [integral_sub_sub_add (hv.const_mul _) (hw.const_mul _)
    (hxv.const_mul _) (hxw.const_mul _)] at hn
  simp only [integral_const_mul] at hn
  nlinarith

theorem integral_mul_exp (a b : ℝ) :
    (∫ x in a..b, x * Real.exp x) = (b - 1) * Real.exp b - (a - 1) * Real.exp a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => ?_) ((continuous_id.mul Real.continuous_exp).intervalIntegrable a b)
  convert! (((hasDerivAt_id x).sub_const 1).mul (Real.hasDerivAt_exp x)) using 1 <;>
    (dsimp; ring)

/-- An increasing weight whose ratio to the exponential decreases has a controlled mean. -/
theorem weighted_interval_mean_bounds {d : ℝ} {w : ℝ → ℝ} (hd : 0 < d)
    (hw : ContinuousOn w (Icc 0 d)) (hW : 0 < ∫ x in Icc 0 d, w x)
    (hm : MonotoneOn w (Icc 0 d))
    (ha : AntitoneOn (fun x => w x / Real.exp x) (Icc 0 d)) :
    d / 2 ≤ (∫ x in Icc 0 d, x * w x) / (∫ x in Icc 0 d, w x) ∧
    (∫ x in Icc 0 d, x * w x) / (∫ x in Icc 0 d, w x) ≤ d / 2 + d ^ 2 / 12 := by
  have hwI := hw.integrableOn_Icc (μ := volume)
  have hxwI := (continuousOn_id.mul hw).integrableOn_Icc (μ := volume)
  have h1I : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc 0 d) :=
    continuous_const.continuousOn.integrableOn_Icc
  have hxI : IntegrableOn (fun x : ℝ => x * 1) (Icc 0 d) :=
    (continuous_id.mul continuous_const).continuousOn.integrableOn_Icc
  have heI := Real.continuous_exp.continuousOn.integrableOn_Icc (a := 0) (b := d)
    (μ := volume)
  have hxeI := (continuous_id.mul Real.continuous_exp).continuousOn.integrableOn_Icc
    (a := 0) (b := d) (μ := volume)
  have hconst : (∫ x in Icc (0 : ℝ) d, (1 : ℝ)) = d := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hd.le,
      intervalIntegral.integral_const]
    simp
  have hid : (∫ x in Icc (0 : ℝ) d, x * 1) = d ^ 2 / 2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hd.le]
    simp [integral_id]
  have hexp : (∫ x in Icc (0 : ℝ) d, Real.exp x) = Real.exp d - 1 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hd.le, integral_exp]
    simp
  have hxexp : (∫ x in Icc (0 : ℝ) d, x * Real.exp x) =
      (d - 1) * Real.exp d + 1 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hd.le, integral_mul_exp]
    simp
  constructor
  · have hc : ∀ᵐ y ∂volume.restrict (Icc 0 d), ∀ᵐ x ∂volume.restrict (Icc 0 d),
        (x - y) * ((1 : ℝ) * w y - w x * 1) ≤ 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rcases le_total x y with hxy | hyx
      · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxy)
          (by simpa using sub_nonneg.mpr (hm hx hy hxy))
      · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hyx)
          (by simpa using sub_nonpos.mpr (hm hy hx hyx))
    have h := weighted_mean_cross_le h1I hwI hxI hxwI hc
    rw [hconst, hid] at h
    rw [le_div_iff₀ hW]
    nlinarith
  · have hc : ∀ᵐ y ∂volume.restrict (Icc 0 d), ∀ᵐ x ∂volume.restrict (Icc 0 d),
        (x - y) * (w x * Real.exp y - Real.exp x * w y) ≤ 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rcases le_total x y with hxy | hyx
      · have hh := (div_le_div_iff₀ (Real.exp_pos y) (Real.exp_pos x)).mp (ha hx hy hxy)
        exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxy) (by nlinarith)
      · have hh := (div_le_div_iff₀ (Real.exp_pos x) (Real.exp_pos y)).mp (ha hy hx hyx)
        exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hyx) (by nlinarith)
    have h := weighted_mean_cross_le hwI heI hxwI hxeI hc
    rw [hexp, hxexp] at h
    have he : 0 < Real.exp d - 1 := by linarith [Real.one_lt_exp_iff.mpr hd]
    have hcomp : (∫ x in Icc 0 d, x * w x) / (∫ x in Icc 0 d, w x) ≤
        ((d - 1) * Real.exp d + 1) / (Real.exp d - 1) :=
      (div_le_div_iff₀ hW he).mpr h
    refine hcomp.trans ?_
    have heq : ((d - 1) * Real.exp d + 1) / (Real.exp d - 1) =
        d * Real.exp d / (Real.exp d - 1) - 1 := by field_simp [he.ne']; ring
    rw [heq]
    exact exponential_mean_le hd

/-- The normalized mean distances obey the precise square-cost bound of Section 4.2. -/
theorem normalized_mean_distance_bounds {d : ℝ} {w : ℝ → ℝ} (hd : 0 < d)
    (hw : ContinuousOn w (Icc 0 d)) (hW : 0 < ∫ x in Icc 0 d, w x)
    (hm : MonotoneOn w (Icc 0 d))
    (ha : AntitoneOn (fun x => w x / Real.exp x) (Icc 0 d)) :
    let u := (∫ x in Icc 0 d, x * w x) / (d * ∫ x in Icc 0 d, w x)
    1 / 2 ≤ u ∧ u ≤ 1 / 2 + d / 12 ∧
      u ^ 2 + (1 - u) ^ 2 ≤ (1 + d ^ 2 / 36) / 2 := by
  dsimp
  have h := weighted_interval_mean_bounds hd hw hW hm ha
  have heq : (∫ x in Icc 0 d, x * w x) / (d * ∫ x in Icc 0 d, w x) =
      ((∫ x in Icc 0 d, x * w x) / (∫ x in Icc 0 d, w x)) / d := by
    field_simp [hd.ne', hW.ne']
  rw [heq]
  have hlo : (1 / 2 : ℝ) ≤ ((∫ x in Icc 0 d, x * w x) /
      (∫ x in Icc 0 d, w x)) / d := (le_div_iff₀ hd).mpr (by linarith [h.1])
  have hhi : ((∫ x in Icc 0 d, x * w x) / (∫ x in Icc 0 d, w x)) / d ≤
      (1 / 2 : ℝ) + d / 12 := (div_le_iff₀ hd).mpr (by nlinarith [h.2])
  refine ⟨hlo, hhi, ?_⟩
  have hs := mul_self_le_mul_self (by linarith : 0 ≤
      ((∫ x in Icc 0 d, x * w x) / (∫ x in Icc 0 d, w x)) / d - 1 / 2)
    (by linarith : ((∫ x in Icc 0 d, x * w x) / (∫ x in Icc 0 d, w x)) / d - 1 / 2 ≤ d / 12)
  nlinarith

end Submission.Obl.Root.MeanDistance
