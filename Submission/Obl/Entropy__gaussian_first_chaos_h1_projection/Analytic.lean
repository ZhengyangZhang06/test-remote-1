import Submission.Obl.Entropy__continuous_jacobian_of_l2_limit.LocalL1

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Submission.Obl.Entropy__gaussian_first_chaos_h1_projection

open Submission.Obl.Entropy__continuous_jacobian_of_l2_limit
open Submission.Lib.GaussianTransport

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "γ" => stdGaussian E

lemma coord_memLp (r : Fin m) : MemLp (fun x : E => x r) 2 γ :=
  IsGaussian.memLp_dual γ (EuclideanSpace.proj r) 2 (by norm_num)

lemma integral_coord (r : Fin m) : (∫ x : E, x r ∂γ) = 0 :=
  integral_strongDual_stdGaussian (EuclideanSpace.proj r)

lemma integral_coord_mul (r s : Fin m) :
    (∫ x : E, x r * x s ∂γ) = if r = s then 1 else 0 := by
  have h := covarianceBilin_apply (μ := γ) IsGaussian.memLp_two_id
    (PiLp.single 2 r (1 : ℝ)) (PiLp.single 2 s (1 : ℝ))
  rw [covarianceBilin_stdGaussian] at h
  change inner ℝ (PiLp.single 2 r (1 : ℝ) : E) (PiLp.single 2 s (1 : ℝ) : E) = _ at h
  simpa [integral_id_stdGaussian, PiLp.inner_apply, PiLp.single_apply] using h.symm

lemma hasFDerivAt_gaussianDensity (x : E) :
    HasFDerivAt gaussianDensity
      (∑ r : Fin m, (∏ s ∈ Finset.univ.erase r, gaussianPDFReal 0 1 (x s)) •
        ((-x r * gaussianPDFReal 0 1 (x r)) • (EuclideanSpace.proj r : E →L[ℝ] ℝ))) x := by
  apply HasFDerivAt.finsetProd (g := fun r (y : E) => gaussianPDFReal 0 1 (y r))
  intro r _
  have h := (hasDerivAt_normalPDF (x r)).comp_hasFDerivAt x
    (EuclideanSpace.proj r : E →L[ℝ] ℝ).hasFDerivAt
  exact h

lemma fderiv_gaussianDensity_coord (x : E) (r : Fin m) :
    fderiv ℝ gaussianDensity x (PiLp.single 2 r (1 : ℝ)) =
      -x r * gaussianDensity x := by
  rw [(hasFDerivAt_gaussianDensity x).fderiv]
  simp only [sum_apply, smul_apply,
    smul_eq_mul, EuclideanSpace.coe_proj, PiLp.single_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [gaussianDensity, ← Finset.mul_prod_erase _ _ (Finset.mem_univ r)]
  ring

/-- Gaussian integration by parts, requiring only integrable terms. -/
lemma gaussian_integral_fderiv {f : E → ℝ} (hf : Differentiable ℝ f)
    (hfi : Integrable f γ) (r : Fin m)
    (hdf : Integrable (fun x => fderiv ℝ f x (PiLp.single 2 r (1 : ℝ))) γ)
    (hxf : Integrable (fun x => x r * f x) γ) :
    (∫ x, fderiv ℝ f x (PiLp.single 2 r (1 : ℝ)) ∂γ) =
      ∫ x, x r * f x ∂γ := by
  have h1 : Integrable (fun x =>
      fderiv ℝ gaussianDensity x (PiLp.single 2 r (1 : ℝ)) * f x) volume := by
    convert (integrable_density_smul hxf).neg using 1
    funext x
    rw [fderiv_gaussianDensity_coord]
    simp only [smul_eq_mul, Pi.neg_apply]
    ring
  have h2 : Integrable (fun x =>
      gaussianDensity x * fderiv ℝ f x (PiLp.single 2 r (1 : ℝ))) volume :=
    integrable_density_smul hdf
  have h3 : Integrable (fun x => gaussianDensity x * f x) volume :=
    integrable_density_smul hfi
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun x _ => (hasFDerivAt_gaussianDensity x).differentiableAt)
    (fun x _ => hf x)
  rw [integral_gaussian_eq_density, integral_gaussian_eq_density]
  rw [h]
  simp_rw [fderiv_gaussianDensity_coord]
  rw [← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

lemma gaussian_integral_fderiv_of_memLp {f : E → ℝ} (hf : Differentiable ℝ f)
    (hfi : MemLp f 2 γ) (r : Fin m)
    (hdf : MemLp (fun x => fderiv ℝ f x (PiLp.single 2 r (1 : ℝ))) 2 γ) :
    (∫ x, fderiv ℝ f x (PiLp.single 2 r (1 : ℝ)) ∂γ) =
      ∫ x, x r * f x ∂γ :=
  gaussian_integral_fderiv hf (hfi.integrable (by norm_num)) r
    (hdf.integrable (by norm_num)) ((coord_memLp r).integrable_mul hfi)

end Submission.Obl.Entropy__gaussian_first_chaos_h1_projection
