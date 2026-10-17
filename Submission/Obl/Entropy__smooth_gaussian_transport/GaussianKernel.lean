import Submission.Obl.Entropy__smooth_gaussian_transport.RadialKernel

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped Topology RealInnerProductSpace NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- The Gaussian kernel at spatial scale r (heat time r²/2). -/
noncomputable def gaussianKernel {m : ℕ} (r : ℝ) (x : E m) : ℝ :=
  (r ^ m)⁻¹ * Submission.Lib.EntropyRemainder.gaussianDensity (r⁻¹ • x)

theorem gaussianKernel_contDiff {m : ℕ} (r : ℝ) {n : WithTop ENat} :
    ContDiff ℝ n (gaussianKernel (m := m) r) := by
  have hs : ContDiff ℝ n (fun x : E m => r⁻¹ • x) := by
    convert! (r⁻¹ • ContinuousLinearMap.id ℝ (E m)).contDiff using 1
  convert! contDiff_const.mul (Submission.Lib.EntropyRemainder.gaussianDensity_contDiff.comp hs) using 1

theorem gaussianKernel_pos {m : ℕ} {r : ℝ} (hr : 0 < r) (x : E m) :
    0 < gaussianKernel r x :=
  mul_pos (inv_pos.mpr (pow_pos hr m)) (Submission.Lib.EntropyRemainder.gaussianDensity_pos _)

theorem gaussianDensity_integrable {m : ℕ} :
    Integrable (Submission.Lib.EntropyRemainder.gaussianDensity (m := m)) volume := by
  simpa only [mul_one] using (Submission.Lib.EntropyRemainder.gaussian_integrable_iff
    (m := m) (f := fun _ => (1 : ℝ))).mp (integrable_const 1)

theorem gaussianDensity_integral {m : ℕ} :
    ∫ x : E m, Submission.Lib.EntropyRemainder.gaussianDensity x = 1 := by
  simpa only [mul_one, integral_const, probReal_univ, smul_eq_mul, one_mul] using
    (Submission.Lib.EntropyRemainder.gaussian_integral_eq (m := m) (fun _ => (1 : ℝ))).symm

theorem gaussianKernel_integrable {m : ℕ} {r : ℝ} (hr : r ≠ 0) :
    Integrable (gaussianKernel (m := m) r) volume :=
  ((integrable_comp_smul_iff volume _ (inv_ne_zero hr)).mpr gaussianDensity_integrable).const_mul _

theorem gaussianKernel_integral {m : ℕ} {r : ℝ} (hr : 0 < r) :
    ∫ x : E m, gaussianKernel r x = 1 := by
  change (∫ x : E m, (r ^ m)⁻¹ * Submission.Lib.EntropyRemainder.gaussianDensity (r⁻¹ • x)) = 1
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume _ hr.le, gaussianDensity_integral]
  simp only [E, finrank_euclideanSpace_fin, smul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (pow_ne_zero _ hr.ne')

theorem gaussianKernel_hasFDerivAt {m : ℕ} (r : ℝ) (x : E m) :
    HasFDerivAt (gaussianKernel r) ((-r⁻¹ ^ 2 * gaussianKernel r x) • innerSL ℝ x) x := by
  have hline : HasFDerivAt (fun y : E m => r⁻¹ • y)
      (r⁻¹ • ContinuousLinearMap.id ℝ (E m)) x := (hasFDerivAt_id x).const_smul r⁻¹
  have hd := ((Submission.Lib.EntropyRemainder.hasFDerivAt_gaussianDensity (r⁻¹ • x)).comp x hline).const_mul
    ((r ^ m)⁻¹)
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    innerSL_apply_apply, smul_eq_mul, real_inner_smul_left, real_inner_smul_right, gaussianKernel]
  ring

theorem gaussianKernel_gradient {m : ℕ} (r : ℝ) (x : E m) :
    gradient (gaussianKernel r) x = (-r⁻¹ ^ 2 * gaussianKernel r x) • x := by
  simp only [gradient, (gaussianKernel_hasFDerivAt r x).fderiv, map_smul]
  congr 1
  exact (toDual ℝ (E m)).symm_apply_apply x

theorem gaussianKernel_gradient_hasFDerivAt {m : ℕ} (r : ℝ) (x : E m) :
    HasFDerivAt (gradient (gaussianKernel r))
      ((r⁻¹ ^ 4 * gaussianKernel r x) • rankOne ℝ x x -
        (r⁻¹ ^ 2 * gaussianKernel r x) • ContinuousLinearMap.id ℝ (E m)) x := by
  have hd := ((gaussianKernel_hasFDerivAt r x).const_mul (-r⁻¹ ^ 2)).smul (hasFDerivAt_id x)
  have he : gradient (gaussianKernel r) = fun y : E m => (-r⁻¹ ^ 2 * gaussianKernel r y) • y :=
    funext (gaussianKernel_gradient r)
  rw [he]
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, rankOne_apply, smul_smul, id_eq]
  module

theorem gaussianKernel_hasDerivAt_scale {m : ℕ} {r : ℝ} (hr : r ≠ 0) (x : E m) :
    HasDerivAt (fun s : ℝ => gaussianKernel s x)
      ((r⁻¹ ^ 3 * ‖x‖ ^ 2 - (m : ℝ) * r⁻¹) * gaussianKernel r x) r := by
  have hd : HasDerivAt (fun s : ℝ => Submission.Lib.EntropyRemainder.gaussianDensity (s⁻¹ • x))
      (r⁻¹ ^ 3 * ‖x‖ ^ 2 * Submission.Lib.EntropyRemainder.gaussianDensity (r⁻¹ • x)) r := by
    convert! (Submission.Lib.EntropyRemainder.hasFDerivAt_gaussianDensity (r⁻¹ • x)).comp_hasDerivAt r
      ((hasDerivAt_inv hr).smul_const x) using 1
    simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, inv_pow]
    ring
  convert! (hasDerivAt_inverse_nat_pow m hr).mul hd using 1
  simp only [gaussianKernel, pow_succ]
  field_simp
  ring

/-- The scale derivative is r times the Euclidean Laplacian. -/
theorem gaussianKernel_heat_equation {m : ℕ} {r : ℝ} (hr : r ≠ 0) (x : E m) :
    deriv (fun s : ℝ => gaussianKernel s x) r =
      r * LinearMap.trace ℝ (E m) (fderiv ℝ (gradient (gaussianKernel r)) x).toLinearMap := by
  have htid : LinearMap.trace ℝ (E m) (ContinuousLinearMap.id ℝ (E m)).toLinearMap = m := by
    change LinearMap.trace ℝ (E m) LinearMap.id = m
    simp only [LinearMap.trace_id, E, finrank_euclideanSpace_fin]
  rw [(gaussianKernel_hasDerivAt_scale hr x).deriv,
    (gaussianKernel_gradient_hasFDerivAt r x).fderiv]
  simp only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_smul,
    map_sub, map_smul, trace_rankOne, real_inner_self_eq_norm_sq,
    htid, smul_eq_mul]
  field_simp

end Submission.Obl.Entropy__smooth_gaussian_transport
