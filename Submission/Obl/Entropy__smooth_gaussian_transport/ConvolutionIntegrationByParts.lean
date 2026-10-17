import Submission.Obl.Entropy__smooth_gaussian_transport.CompactDifferentiation

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace Convolution NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem convolution_integral_fderiv_right {m : ℕ} {f g : E m → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 1 g) (x v : E m) :
    (∫ y, f y * fderiv ℝ g (x - y) v) = ∫ y, fderiv ℝ f y v * g (x - y) := by
  let k : E m → ℝ := fun y => g (x - y)
  have hk : ContDiff ℝ 1 k := hg.comp (contDiff_const.sub contDiff_id)
  have he (y : E m) : fderiv ℝ k y v = -fderiv ℝ g (x - y) v := by
    have hd := (hg.differentiable_one (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    rw [show fderiv ℝ k y =
        (fderiv ℝ g (x - y)).comp (0 - ContinuousLinearMap.id ℝ (E m)) from hd.fderiv]
    simp
  have hdf : Continuous (fun y => fderiv ℝ f y v) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdg : Continuous (fun y => fderiv ℝ g (x - y) v) :=
    ((hg.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)).clm_apply continuous_const
  have hdfk : Integrable (fun y => fderiv ℝ f y v * k y) volume :=
    (hdf.mul hk.continuous).integrable_of_hasCompactSupport (hfc.fderiv_apply ℝ v).mul_right
  have hfdg : Integrable (fun y => f y * fderiv ℝ g (x - y) v) volume :=
    (hf.continuous.mul hdg).integrable_of_hasCompactSupport hfc.mul_right
  have hfdk : Integrable (fun y => f y * fderiv ℝ k y v) volume := by
    convert! hfdg.neg using 1
    funext y
    simp only [he, mul_neg, Pi.neg_apply]
  have hfk : Integrable (fun y => f y * k y) volume :=
    (hf.continuous.mul hk.continuous).integrable_of_hasCompactSupport hfc.mul_right
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    hdfk hfdk hfk (fun y _ => hf.differentiable_one y) (fun y _ => hk.differentiable_one y)
  simpa only [he, mul_neg, integral_neg, neg_inj] using hh

theorem convolution_integral_second_fderiv_right {m : ℕ} {f g : E m → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (x v : E m) :
    (∫ y, f y * fderiv ℝ (fun z => fderiv ℝ g z v) (x - y) v) =
      ∫ y, fderiv ℝ (fun z => fderiv ℝ f z v) y v * g (x - y) := by
  have hdf : ContDiff ℝ 1 (fun z => fderiv ℝ f z v) :=
    (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hdg : ContDiff ℝ 1 (fun z => fderiv ℝ g z v) :=
    (hg.fderiv_right (by norm_num)).clm_apply contDiff_const
  rw [convolution_integral_fderiv_right (hf.of_le (by norm_num)) hfc hdg x v,
    convolution_integral_fderiv_right hdf (hfc.fderiv_apply ℝ v) (hg.of_le (by norm_num)) x v]

end Submission.Obl.Entropy__smooth_gaussian_transport
