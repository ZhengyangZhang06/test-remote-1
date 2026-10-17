import Submission.Obl.Entropy__normalized_remainder.GaussianDensity
import Submission.Obl.Entropy__normalized_remainder.FirstChaos

/-!
# Gaussian integration by parts

Global directional integration by parts under precisely the integrability
assumptions needed for applying the Lebesgue version to the Gaussian density.
-/

namespace Submission.Obl.Entropy__normalized_remainder

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

end Submission.Obl.Entropy__normalized_remainder
