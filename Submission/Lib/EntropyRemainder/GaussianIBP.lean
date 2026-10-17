/-
Adapted from: here:o006

Original proofs by sessions x0016, x0019 and x0062.
-/

import Submission.Lib.EntropyRemainder.GaussianDensity
import Submission.Lib.EntropyRemainder.FirstChaos

/-!
# Gaussian integration by parts

Global directional integration by parts under precisely the integrability
assumptions needed for applying the Lebesgue version to the Gaussian density.
-/

set_option backward.isDefEq.respectTransparency false

namespace Submission.Lib.EntropyRemainder

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

/-- Stein's identity, with all three required integrability assumptions explicit. -/
theorem gaussian_integral_fderiv {m : ℕ} {f : E m → ℝ} (v : E m)
    (hd : Differentiable ℝ f)
    (hf : Integrable f (stdGaussian (E m)))
    (hdf : Integrable (fun x => fderiv ℝ f x v) (stdGaussian (E m)))
    (hxf : Integrable (fun x => inner ℝ x v * f x) (stdGaussian (E m))) :
    (∫ x, fderiv ℝ f x v ∂stdGaussian (E m)) =
      ∫ x, inner ℝ x v * f x ∂stdGaussian (E m) := by
  have hρf := gaussian_integrable_iff.mp hf
  have hρdf := gaussian_integrable_iff.mp hdf
  have hρxf := gaussian_integrable_iff.mp hxf
  have hdρf : Integrable (fun x => fderiv ℝ gaussianDensity x v * f x) := by
    simpa only [fderiv_gaussianDensity, neg_mul, mul_assoc, Pi.neg_apply] using! hρxf.neg
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hdρf hρdf hρf
    (fun x _ => (hasFDerivAt_gaussianDensity x).differentiableAt) (fun x _ => hd x)
  simpa only [gaussian_integral_eq, fderiv_gaussianDensity, neg_mul, mul_assoc,
    integral_neg, neg_neg] using h

/-- In particular every square-integrable derivative has its expected first coefficient. -/
theorem gaussian_integral_coordinateDerivative {m : ℕ} {f : E m → ℝ}
    (hd : Differentiable ℝ f) (hf : MemLp f 2 (stdGaussian (E m)))
    (r : Fin m)
    (hdf : MemLp (fun x => fderiv ℝ f x (PiLp.single 2 r (1 : ℝ)))
      2 (stdGaussian (E m))) :
    (∫ x, fderiv ℝ f x (PiLp.single 2 r (1 : ℝ)) ∂stdGaussian (E m)) =
      ∫ x, x r * f x ∂stdGaussian (E m) := by
  have hi (x : E m) : inner ℝ x (PiLp.single 2 r (1 : ℝ)) = x r := by
    simp [PiLp.inner_apply]
  simpa only [hi] using gaussian_integral_fderiv (PiLp.single 2 r (1 : ℝ)) hd
    (hf.integrable (by norm_num)) (hdf.integrable (by norm_num))
    (by simpa only [hi, Pi.mul_apply] using! (gaussian_coord_memLp r).integrable_mul hf)

/-- The Gaussian product rule in a form usable for matrix entries. -/
theorem gaussian_integral_mul_fderiv {m : ℕ} {f g : E m → ℝ} (v : E m)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfg : Integrable (fun x => f x * g x) (stdGaussian (E m)))
    (hdfg : Integrable (fun x => fderiv ℝ f x v * g x) (stdGaussian (E m)))
    (hfdg : Integrable (fun x => f x * fderiv ℝ g x v) (stdGaussian (E m)))
    (hxfg : Integrable (fun x => inner ℝ x v * (f x * g x)) (stdGaussian (E m))) :
    (∫ x, f x * fderiv ℝ g x v ∂stdGaussian (E m)) =
      (∫ x, inner ℝ x v * (f x * g x) ∂stdGaussian (E m)) -
      ∫ x, fderiv ℝ f x v * g x ∂stdGaussian (E m) := by
  have hd (x : E m) : fderiv ℝ (fun y => f y * g y) x v =
      fderiv ℝ f x v * g x + f x * fderiv ℝ g x v := by
    erw [fderiv_mul (hf x) (hg x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hi : Integrable (fun x => fderiv ℝ (fun y => f y * g y) x v)
      (stdGaussian (E m)) := by
    simpa only [hd] using! hdfg.add hfdg
  have h := gaussian_integral_fderiv (f := fun y => f y * g y) v (hf.mul hg) hfg hi hxfg
  simp only [hd, integral_add hdfg hfdg] at h
  linarith

/-- A compact test needs no growth or global integrability assumptions on the coefficient. -/
theorem gaussian_integral_mul_fderiv_compact {m : ℕ} {f g : E m → ℝ} (v : E m)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    (∫ x, f x * fderiv ℝ g x v ∂stdGaussian (E m)) =
      (∫ x, inner ℝ x v * (f x * g x) ∂stdGaussian (E m)) -
      ∫ x, fderiv ℝ f x v * g x ∂stdGaussian (E m) := by
  have hdf : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdg : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  apply gaussian_integral_mul_fderiv v hf.differentiable_one hg.differentiable_one
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  · exact (hdf.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  · exact (hf.continuous.mul hdg).integrable_of_hasCompactSupport
      (hgc.fderiv_apply ℝ v).mul_left
  · exact ((continuous_id.inner continuous_const).mul
      (hf.continuous.mul hg.continuous)).integrable_of_hasCompactSupport
        hgc.mul_left.mul_left

/-- The coordinate adjoint is `x_r f - partial_r f`. -/
theorem gaussian_coordinate_adjoint_compact {m : ℕ} {f g : E m → ℝ}
    (r : Fin m) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) :
    (∫ x, f x * fderiv ℝ g x (PiLp.single 2 r (1 : ℝ)) ∂stdGaussian (E m)) =
      ∫ x, (x r * f x - fderiv ℝ f x (PiLp.single 2 r (1 : ℝ))) * g x
        ∂stdGaussian (E m) := by
  have hdf : Continuous (fun x => fderiv ℝ f x (PiLp.single 2 r (1 : ℝ))) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hi₁ : Integrable (fun x => x r * f x * g x) (stdGaussian (E m)) :=
    ((by fun_prop : Continuous (fun x : E m => x r * f x * g x))).integrable_of_hasCompactSupport
      hgc.mul_left
  have hi₂ : Integrable (fun x => fderiv ℝ f x (PiLp.single 2 r (1 : ℝ)) * g x)
      (stdGaussian (E m)) :=
    (hdf.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  simp_rw [sub_mul]
  rw [integral_sub hi₁ hi₂]
  have hi (x : E m) : inner ℝ x (PiLp.single 2 r (1 : ℝ)) = x r := by
    simp [PiLp.inner_apply]
  simpa only [hi, mul_assoc] using gaussian_integral_mul_fderiv_compact
      (PiLp.single 2 r (1 : ℝ)) hf hg hgc

end Submission.Lib.EntropyRemainder
