import Submission.Obl.Entropy__smooth_gaussian_transport.CompactScaleDifferentiation
import Submission.Obl.Entropy__smooth_gaussian_transport.GaussianSmoothing
import Submission.Obl.Entropy__smooth_gaussian_transport.GaussianKernelMoments

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace Convolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem gaussianKernel_joint_continuous {m : ℕ} :
    ContinuousOn (fun z : ℝ × E m => gaussianKernel z.1 z.2) (Ioi 0 ×ˢ univ) := by
  have hi : ContinuousOn (fun z : ℝ × E m => z.1⁻¹) (Ioi 0 ×ˢ univ) :=
    continuous_fst.continuousOn.inv₀ (fun z hz => ne_of_gt hz.1)
  have hs : ContinuousOn (fun z : ℝ × E m => z.1⁻¹ • z.2) (Ioi 0 ×ˢ univ) :=
    hi.smul continuous_snd.continuousOn
  have hh := (hi.pow m).mul (Submission.Lib.EntropyRemainder.gaussianDensity_continuous.comp_continuousOn hs)
  convert! hh using 1
  funext z
  simp only [gaussianKernel, Pi.mul_apply, Pi.pow_apply, Function.comp_apply, inv_pow]

theorem gaussianKernel_derivative_joint_continuous {m : ℕ} (n : ℕ) :
    ContinuousOn (fun z : ℝ × E m => iteratedFDeriv ℝ n (gaussianKernel z.1) z.2)
      (Ioi 0 ×ˢ univ) := by
  have hi : ContinuousOn (fun z : ℝ × E m => z.1⁻¹) (Ioi 0 ×ˢ univ) :=
    continuous_fst.continuousOn.inv₀ (fun z hz => ne_of_gt hz.1)
  have hs : ContinuousOn (fun z : ℝ × E m => z.1⁻¹ • z.2) (Ioi 0 ×ˢ univ) :=
    hi.smul continuous_snd.continuousOn
  have hd : Continuous (iteratedFDeriv ℝ n (Submission.Lib.EntropyRemainder.gaussianDensity (m := m))) :=
    (Submission.Lib.EntropyRemainder.gaussianDensity_contDiff (n := (n : WithTop ENat))).continuous_iteratedFDeriv le_rfl
  convert! (hi.pow (m + n)).smul (hd.comp_continuousOn hs) using 1
  funext z
  change iteratedFDeriv ℝ n (gaussianKernel z.1) z.2 =
    z.1⁻¹ ^ (m + n) • iteratedFDeriv ℝ n Submission.Lib.EntropyRemainder.gaussianDensity (z.1⁻¹ • z.2)
  rw [gaussianKernel_iteratedFDeriv, inv_pow]

theorem gaussianKernel_scale_derivative_continuous {m : ℕ} :
    ContinuousOn (fun z : ℝ × E m =>
      (z.1⁻¹ ^ 3 * ‖z.2‖ ^ 2 - (m : ℝ) * z.1⁻¹) * gaussianKernel z.1 z.2)
      (Ioi 0 ×ˢ univ) := by
  have hi : ContinuousOn (fun z : ℝ × E m => z.1⁻¹) (Ioi 0 ×ˢ univ) :=
    continuous_fst.continuousOn.inv₀ (fun z hz => ne_of_gt hz.1)
  exact (((hi.pow 3).mul (continuous_snd.norm.pow 2).continuousOn).sub
    (continuousOn_const.mul hi)).mul gaussianKernel_joint_continuous

theorem gaussianSmoothing_hasDerivAt_scale {m : ℕ} {r : ℝ} (hr : 0 < r)
    {f : E m → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (x : E m) :
    HasDerivAt (fun s => gaussianSmoothing s f x)
      (∫ y, f y * deriv (fun s : ℝ => gaussianKernel s (x - y)) r) r := by
  have hp : Continuous (fun z : ℝ × E m => (z.1, x - z.2)) :=
    continuous_fst.prodMk (continuous_const.sub continuous_snd)
  have hmap : MapsTo (fun z : ℝ × E m => (z.1, x - z.2))
      (Ioi 0 ×ˢ univ) (Ioi 0 ×ˢ univ) := fun z hz => ⟨hz.1, mem_univ _⟩
  have hh := compact_integral_hasDerivAt hf hfc
    (gaussianKernel_joint_continuous.comp hp.continuousOn hmap)
    (gaussianKernel_scale_derivative_continuous.comp hp.continuousOn hmap)
    (fun s hs y => gaussianKernel_hasDerivAt_scale (ne_of_gt hs) (x - y)) hr
  convert! hh using 1
  apply integral_congr_ae
  filter_upwards [] with y
  rw [(gaussianKernel_hasDerivAt_scale hr.ne' (x - y)).deriv]
  rfl

end Submission.Obl.Entropy__smooth_gaussian_transport
