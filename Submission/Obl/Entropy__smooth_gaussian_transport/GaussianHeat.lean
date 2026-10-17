import Submission.Obl.Entropy__smooth_gaussian_transport.GaussianScale
import Submission.Obl.Entropy__smooth_gaussian_transport.ConvolutionIntegrationByParts

open MeasureTheory Set Filter InnerProductSpace
open scoped Topology RealInnerProductSpace Convolution BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def laplacian {m : ℕ} (f : E m → ℝ) (x : E m) : ℝ :=
  ∑ i : Fin m, fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.basisFun (Fin m) ℝ i)) x
    (EuclideanSpace.basisFun (Fin m) ℝ i)

theorem laplacian_continuous {m : ℕ} {f : E m → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (laplacian f) := by
  apply continuous_finset_sum
  intro i hi
  have hd : ContDiff ℝ 1 (fun z => fderiv ℝ f z (EuclideanSpace.basisFun (Fin m) ℝ i)) :=
    (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
  exact (hd.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem laplacian_hasCompactSupport {m : ℕ} {f : E m → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (laplacian f) := by
  have hh : HasCompactSupport (∑ i : Fin m, fun x =>
      fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.basisFun (Fin m) ℝ i)) x
        (EuclideanSpace.basisFun (Fin m) ℝ i)) :=
    HasCompactSupport.finset_sum (fun i _ =>
      (hf.fderiv_apply ℝ (EuclideanSpace.basisFun (Fin m) ℝ i)).fderiv_apply ℝ _)
  convert! hh using 1
  funext x
  simp only [laplacian, Finset.sum_apply]

theorem directional_second_eq_gradient_derivative {m : ℕ} {f : E m → ℝ} {x : E m}
    (hd : DifferentiableAt ℝ (gradient f) x) (v : E m) :
    fderiv ℝ (fun z => fderiv ℝ f z v) x v = inner ℝ (fderiv ℝ (gradient f) x v) v := by
  let B : E m →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ v).comp (toDual ℝ (E m)).toContinuousLinearMap
  have hh : HasFDerivAt (fun z => fderiv ℝ f z v) (B.comp (fderiv ℝ (gradient f) x)) x := by
    convert! B.hasFDerivAt.comp x hd.hasFDerivAt using 1
    funext z
    exact congrArg (fun p : E m →L[ℝ] ℝ => p v) (toDual_gradient (𝕜 := ℝ) (f := f) (x := z)).symm
  rw [hh.fderiv]
  rfl

theorem laplacian_eq_trace {m : ℕ} {f : E m → ℝ} {x : E m}
    (hd : DifferentiableAt ℝ (gradient f) x) :
    laplacian f x = LinearMap.trace ℝ (E m) (fderiv ℝ (gradient f) x).toLinearMap := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin m) ℝ)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [directional_second_eq_gradient_derivative hd]
  exact real_inner_comm _ _

theorem convolution_integral_laplacian {m : ℕ} {f g : E m → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (x : E m) :
    (∫ y, f y * laplacian g (x - y)) = ∫ y, laplacian f y * g (x - y) := by
  have hi (i : Fin m) : Integrable (fun y => f y *
      fderiv ℝ (fun z => fderiv ℝ g z (EuclideanSpace.basisFun (Fin m) ℝ i)) (x - y)
        (EuclideanSpace.basisFun (Fin m) ℝ i)) volume := by
    have hd : ContDiff ℝ 1 (fun z => fderiv ℝ g z (EuclideanSpace.basisFun (Fin m) ℝ i)) :=
      (hg.fderiv_right (by norm_num)).clm_apply contDiff_const
    exact (hf.continuous.mul (((hd.continuous_fderiv one_ne_zero).comp
      (continuous_const.sub continuous_id)).clm_apply continuous_const)).integrable_of_hasCompactSupport hfc.mul_right
  have hj (i : Fin m) : Integrable (fun y =>
      fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.basisFun (Fin m) ℝ i)) y
        (EuclideanSpace.basisFun (Fin m) ℝ i) * g (x - y)) volume := by
    have hd : ContDiff ℝ 1 (fun z => fderiv ℝ f z (EuclideanSpace.basisFun (Fin m) ℝ i)) :=
      (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
    exact (((hd.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
      (hg.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
        ((hfc.fderiv_apply ℝ _).fderiv_apply ℝ _).mul_right
  simp only [laplacian, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finset_sum _ (fun i _ => hi i), integral_finset_sum _ (fun i _ => hj i)]
  apply Finset.sum_congr rfl
  intro i hi'
  exact convolution_integral_second_fderiv_right hf hfc hg x _

/-- Gaussian smoothing of a compact C² function solves the heat equation in scale form. -/
theorem gaussianSmoothing_heat_equation {m : ℕ} {r : ℝ} (hr : 0 < r)
    {f : E m → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (x : E m) :
    HasDerivAt (fun s => gaussianSmoothing s f x) (r * gaussianSmoothing r (laplacian f) x) r := by
  have hh := gaussianSmoothing_hasDerivAt_scale hr hf.continuous hfc x
  have he : (∫ y, f y * deriv (fun s : ℝ => gaussianKernel s (x - y)) r) =
      r * gaussianSmoothing r (laplacian f) x := by
    have hpoint (y : E m) : deriv (fun s : ℝ => gaussianKernel s (x - y)) r =
        r * laplacian (gaussianKernel r) (x - y) := by
      rw [gaussianKernel_heat_equation hr.ne', laplacian_eq_trace
        (gaussianKernel_gradient_hasFDerivAt r (x - y)).differentiableAt]
    simp_rw [hpoint, mul_left_comm (f _) r]
    rw [integral_const_mul, convolution_integral_laplacian hf hfc (gaussianKernel_contDiff r) x]
    rfl
  rwa [he] at hh

end Submission.Obl.Entropy__smooth_gaussian_transport
