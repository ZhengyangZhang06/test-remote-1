import Submission.Obl.Entropy__smooth_gaussian_transport.DirectionalQuotient

open MeasureTheory Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem directionalQuotient_error_bound {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {f : X → Y} (hf : ContDiff ℝ 1 f) {h : ℝ} (hh : h ≠ 0) (v x : X) {M : ℝ}
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ f (x + t • (h • v)) - fderiv ℝ f x‖ ≤ M) :
    ‖directionalQuotient f h v x - fderiv ℝ f x v‖ ≤ M * ‖v‖ := by
  have hc : Continuous (fun t : ℝ => fderiv ℝ f (x + t • (h • v)) v) :=
    ((hf.continuous_fderiv (by norm_num)).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  have he : (∫ t in (0 : ℝ)..1, fderiv ℝ f x v) = fderiv ℝ f x v := by simp
  rw [directionalQuotient_eq_integral hf hh, ← he,
    ← intervalIntegral.integral_sub (hc.intervalIntegrable 0 1) intervalIntegrable_const]
  apply interval_average_norm_bound
  intro t ht
  calc
    _ = ‖(fderiv ℝ f (x + t • (h • v)) - fderiv ℝ f x) v‖ := rfl
    _ ≤ ‖fderiv ℝ f (x + t • (h • v)) - fderiv ℝ f x‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (hb t ht) (norm_nonneg v)

theorem directionalQuotient_tendstoUniformlyOn_of_holder {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {f : X → Y} (hf : ContDiff ℝ 1 f) {h : ℕ → ℝ} (hh : ∀ n, h n ≠ 0)
    (hlim : Tendsto h atTop (nhds 0)) (v : X) {K : Set X} {C α : ℝ}
    (hα : 0 < α)
    (hb : ∀ n x, x ∈ K → ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ f (x + t • (h n • v)) - fderiv ℝ f x‖ ≤ C * (|h n| * ‖v‖) ^ α) :
    TendstoUniformlyOn (fun n => directionalQuotient f (h n) v)
      (fun x => fderiv ℝ f x v) atTop K := by
  have hl : Tendsto (fun n => (C * (|h n| * ‖v‖) ^ α) * ‖v‖) atTop (nhds 0) := by
    have hbase : Tendsto (fun n => |h n| * ‖v‖) atTop (nhds 0) := by
      simpa only [abs_zero, zero_mul] using hlim.abs.mul_const ‖v‖
    simpa only [Real.zero_rpow hα.ne', mul_zero, zero_mul, Function.comp_apply] using
      (((Real.continuous_rpow_const hα.le).tendsto 0).comp hbase).const_mul C |>.mul_const ‖v‖
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hl.eventually (eventually_lt_nhds hε)] with n hn
  intro x hx
  rw [dist_eq_norm, norm_sub_rev]
  exact (directionalQuotient_error_bound hf (hh n) v x (hb n x hx)).trans_lt hn

end Submission.Obl.Entropy__smooth_gaussian_transport
