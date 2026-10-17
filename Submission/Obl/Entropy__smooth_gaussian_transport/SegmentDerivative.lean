import Submission.Obl.Entropy__smooth_gaussian_transport.SegmentMean

open MeasureTheory Set

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem segmentMean_fderiv_apply {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℝ} (hf : ContDiff ℝ 1 f) (a b : X) :
    segmentMean (fderiv ℝ f) a b (b - a) = f b - f a := by
  have hc : Continuous (fun t : ℝ => fderiv ℝ f ((1 - t) • a + t • b)) :=
    (hf.continuous_fderiv (by norm_num)).comp (by fun_prop)
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => f ((1 - t) • a + t • b))
      (fderiv ℝ f ((1 - t) • a + t • b) (b - a)) t := by
    convert! (hf.differentiable_one _).hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const a |>.add
        ((hasDerivAt_id t).smul_const b)) using 1 <;> simp <;> module
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((hc.clm_apply continuous_const).intervalIntegrable 0 1)
  simp only [sub_self, zero_smul, one_smul, zero_add, sub_zero, add_zero] at he
  change (∫ t in (0 : ℝ)..1, fderiv ℝ f ((1 - t) • a + t • b)) (b - a) = _
  rw [ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable 0 1)]
  exact he

end Submission.Obl.Entropy__smooth_gaussian_transport
