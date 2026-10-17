import Submission.Obl.Entropy__continuous_jacobian_of_l2_limit.LocalL1

open MeasureTheory ProbabilityTheory
open Submission.Lib.GaussianTransport
open Submission.Obl.Entropy__continuous_jacobian_of_l2_limit
open scoped ContDiff

namespace Submission.Obl.Entropy__gaussian_weak_remainder_witnesses

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

lemma smooth_gaussianDensity : ContDiff ℝ ∞ (gaussianDensity : E → ℝ) := by
  apply contDiff_prod
  intro i _
  exact contDiff_normalPDF.comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

lemma gaussianDensity_partial (x : E) (r : Fin m) :
    fderiv ℝ gaussianDensity x (PiLp.single 2 r (1 : ℝ)) = -x r * gaussianDensity x := by
  have hd (i : Fin m) : HasFDerivAt (fun y : E => normalPDF (y i))
      ((-x i * normalPDF (x i)) • EuclideanSpace.proj (𝕜 := ℝ) i) x := by
    exact
      (hasDerivAt_normalPDF (x i)).comp_hasFDerivAt x (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
  have h := (HasFDerivAt.finsetProd (u := Finset.univ) (fun i _ => hd i)).fderiv
  change fderiv ℝ (fun y : E => ∏ i, normalPDF (y i)) x _ = _
  rw [h]
  simp only [sum_apply, smul_apply, smul_eq_mul,
    EuclideanSpace.proj, PiLp.proj_apply, PiLp.single_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change (∏ j ∈ Finset.univ.erase r, normalPDF (x j)) * (-x r * normalPDF (x r)) =
    -x r * ∏ j, normalPDF (x j)
  rw [← Finset.mul_prod_erase Finset.univ (fun j => normalPDF (x j)) (Finset.mem_univ r)]
  ring

/-- Gaussian integration by parts with a compact test function. Only C1 regularity
of the multiplier is needed, with no growth restriction away from the test's support. -/
lemma gaussian_product_ibp {F z : E → ℝ} (hF : ContDiff ℝ 1 F)
    (hz : ContDiff ℝ 1 z) (hzc : HasCompactSupport z) (r : Fin m) :
    (∫ x, (x r * F x - fderiv ℝ F x (PiLp.single 2 r (1 : ℝ))) * z x
      ∂stdGaussian E) =
    ∫ x, F x * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)) ∂stdGaussian E := by
  let v : E := PiLp.single 2 r (1 : ℝ)
  have hcF : Continuous (fun x => fderiv ℝ F x v) :=
    (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcz : Continuous (fun x => fderiv ℝ z x v) :=
    (hz.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hρF : ContDiff ℝ 1 (fun x => gaussianDensity x * F x) :=
    (smooth_gaussianDensity.of_le (by simp)).mul hF
  have hd (x : E) : fderiv ℝ (fun x => gaussianDensity x * F x) x v =
      gaussianDensity x * (fderiv ℝ F x v - x r * F x) := by
    rw [fderiv_fun_mul (smooth_gaussianDensity.differentiable (by simp) x)
      (hF.differentiable (by norm_num) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [gaussianDensity_partial x r]
    ring
  have h1 : Integrable (fun x => fderiv ℝ (fun x => gaussianDensity x * F x) x v * z x)
      (volume : Measure E) := by
    exact (((hρF.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
      hz.continuous).integrable_of_hasCompactSupport hzc.mul_left
  have h2 : Integrable (fun x => (gaussianDensity x * F x) * fderiv ℝ z x v)
      (volume : Measure E) := by
    exact (hρF.continuous.mul hcz).integrable_of_hasCompactSupport
      (hzc.fderiv_apply ℝ v).mul_left
  have h3 : Integrable (fun x => (gaussianDensity x * F x) * z x)
      (volume : Measure E) :=
    (hρF.continuous.mul hz.continuous).integrable_of_hasCompactSupport hzc.mul_left
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun x _ => hρF.differentiable (by norm_num) x)
    (fun x _ => hz.differentiable (by norm_num) x)
  simp_rw [hd] at hi
  rw [integral_gaussian_eq_density, integral_gaussian_eq_density]
  change (∫ x, gaussianDensity x * ((x r * F x - fderiv ℝ F x v) * z x)) =
    ∫ x, gaussianDensity x * (F x * fderiv ℝ z x v)
  calc
    _ = -(∫ x, gaussianDensity x * (fderiv ℝ F x v - x r * F x) * z x) := by
      rw [← integral_neg]
      congr 1
      funext x
      ring
    _ = ∫ x, (gaussianDensity x * F x) * fderiv ℝ z x v := hi.symm
    _ = _ := by congr 1; funext x; ring

end Submission.Obl.Entropy__gaussian_weak_remainder_witnesses
