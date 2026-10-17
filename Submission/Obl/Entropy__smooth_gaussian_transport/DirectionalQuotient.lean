import Mathlib

open MeasureTheory Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def directionalQuotient {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X → Y) (h : ℝ) (v : X) (x : X) : Y := h⁻¹ • (f (x + h • v) - f x)

theorem directionalQuotient_contDiff {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {n : WithTop ENat} (hf : ContDiff ℝ n f) (h : ℝ) (v : X) :
    ContDiff ℝ n (directionalQuotient f h v) :=
  ((hf.comp (contDiff_id.add contDiff_const)).sub hf).const_smul h⁻¹

theorem directionalQuotient_fderiv {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} (hf : Differentiable ℝ f) (h : ℝ) (v x : X) :
    fderiv ℝ (directionalQuotient f h v) x = directionalQuotient (fderiv ℝ f) h v x := by
  have hd := ((hf (x + h • v)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const (h • v)))
  convert! ((hd.sub (hf x).hasFDerivAt).const_smul h⁻¹).fderiv using 1

theorem directionalQuotient_iteratedFDeriv {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {n : ℕ} (hf : ContDiff ℝ n f) (h : ℝ) (v x : X) :
    iteratedFDeriv ℝ n (directionalQuotient f h v) x =
      directionalQuotient (iteratedFDeriv ℝ n f) h v x := by
  have hs : ContDiff ℝ n (fun z => f (z + h • v)) := hf.comp (contDiff_id.add contDiff_const)
  have hsub := iteratedFDeriv_sub_apply (hs.contDiffAt (x := x)) (hf.contDiffAt (x := x))
  change iteratedFDeriv ℝ n (fun z => f (z + h • v) - f z) x = _ at hsub
  change iteratedFDeriv ℝ n (fun z => h⁻¹ • (f (z + h • v) - f z)) x = _
  rw [iteratedFDeriv_const_smul_apply' (hs.sub hf).contDiffAt,
    hsub, iteratedFDeriv_comp_add_right]
  rfl

/-- A difference quotient is the average of the derivative on the joining
segment. This identity supplies estimates independent of the step size. -/
theorem directionalQuotient_eq_integral {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {f : X → Y} (hf : ContDiff ℝ 1 f) {h : ℝ} (hh : h ≠ 0) (v x : X) :
    directionalQuotient f h v x = ∫ t in (0 : ℝ)..1, fderiv ℝ f (x + t • (h • v)) v := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => f (x + t • (h • v)))
      (h • (fderiv ℝ f (x + t • (h • v)) v)) t := by
    convert! ((hf.differentiable_one _).hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const (h • v)).const_add x)) using 1
    simp only [one_smul, map_smul, id_eq]
  have hc : Continuous (fun t : ℝ => h • (fderiv ℝ f (x + t • (h • v)) v)) :=
    (((hf.continuous_fderiv (by norm_num)).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const).const_smul h
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hc.intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, add_zero, intervalIntegral.integral_smul] at he
  dsimp only [directionalQuotient]
  rw [← he, smul_smul, inv_mul_cancel₀ hh, one_smul]

theorem interval_average_norm_bound {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : ℝ → Y} {C : ℝ} (hf : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ C) :
    ‖∫ t in (0 : ℝ)..1, f t‖ ≤ C := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  simpa only [sub_zero, abs_one, mul_one] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (a := 0) (b := 1)
      (fun t ht => hf t (by simpa only [min_eq_left h01, max_eq_right h01] using Ioc_subset_Icc_self ht)))

theorem directionalQuotient_norm_bound {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {f : X → Y} (hf : ContDiff ℝ 1 f) {h : ℝ} (hh : h ≠ 0) (v x : X) {M : ℝ}
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ f (x + t • (h • v))‖ ≤ M) :
    ‖directionalQuotient f h v x‖ ≤ M * ‖v‖ := by
  rw [directionalQuotient_eq_integral hf hh]
  exact interval_average_norm_bound (fun t ht =>
    ((fderiv ℝ f (x + t • (h • v))).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hb t ht) (norm_nonneg v)))

theorem directionalQuotient_holder_bound {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {f : X → Y} (hf : ContDiff ℝ 1 f) {h : ℝ} (hh : h ≠ 0) (v x y : X) {C α : ℝ}
    (hb : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ f (x + t • (h • v)) - fderiv ℝ f (y + t • (h • v))‖ ≤ C * ‖x - y‖ ^ α) :
    ‖directionalQuotient f h v x - directionalQuotient f h v y‖ ≤
      (C * ‖v‖) * ‖x - y‖ ^ α := by
  have hc (z : X) : Continuous (fun t : ℝ => fderiv ℝ f (z + t • (h • v)) v) :=
    ((hf.continuous_fderiv (by norm_num)).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  rw [directionalQuotient_eq_integral hf hh, directionalQuotient_eq_integral hf hh,
    ← intervalIntegral.integral_sub ((hc x).intervalIntegrable 0 1) ((hc y).intervalIntegrable 0 1)]
  apply interval_average_norm_bound
  intro t ht
  calc
    _ = ‖(fderiv ℝ f (x + t • (h • v)) - fderiv ℝ f (y + t • (h • v))) v‖ := rfl
    _ ≤ ‖fderiv ℝ f (x + t • (h • v)) - fderiv ℝ f (y + t • (h • v))‖ * ‖v‖ :=
      ContinuousLinearMap.le_opNorm _ v
    _ ≤ (C * ‖x - y‖ ^ α) * ‖v‖ := mul_le_mul_of_nonneg_right (hb t ht) (norm_nonneg v)
    _ = _ := by ring

end Submission.Obl.Entropy__smooth_gaussian_transport
