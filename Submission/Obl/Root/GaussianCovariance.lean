import Submission.Obl.Entropy__gaussian_first_chaos_h1_projection.Projection
import Submission.Obl.Entropy__gaussian_covariance_variational.Scalar
import Submission.Lib.GaussianTransport.GaussianMatrixMean

/-!
# Covariance bounds for the normalization zeros

The Gaussian first-chaos projection gives the lower covariance bound in
Proposition 2.3. The upper bound is the sharp Gaussian Poincare estimate,
obtained by specializing the accepted weak covariance inequality.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators MatrixOrder

namespace Submission.Obl.Root.GaussianCovariance

open Submission.Lib.EntropyTools
open Submission.Obl.Entropy__gaussian_first_chaos_h1_projection
open Submission.Obl.Entropy__gaussian_covariance_variational

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "γ" => stdGaussian E
local notation "Mat" => Matrix (Fin m) (Fin m) ℝ

/-- The first Gaussian chaos of a scalar map is controlled by its variance. -/
theorem mean_derivative_sq_le_variance {f : E → ℝ}
    (hf : Differentiable ℝ f) (hf2 : MemLp f 2 γ)
    (hdf : ∀ r, MemLp (fun x => fderiv ℝ f x (PiLp.single 2 r (1 : ℝ))) 2 γ) :
    (∑ r, (∫ x, fderiv ℝ f x (PiLp.single 2 r (1 : ℝ)) ∂γ)^2) ≤
      ∫ x, (f x - ∫ y, f y ∂γ)^2 ∂γ := by
  let g : E → ℝ := fun x => f x - ∫ y, f y ∂γ
  have hg : MemLp g 2 γ := hf2.sub (memLp_const _)
  have hc (r : Fin m) : firstCoeff g r =
      ∫ x, fderiv ℝ f x (PiLp.single 2 r (1 : ℝ)) ∂γ := by
    rw [gaussian_integral_fderiv_of_memLp hf hf2 r (hdf r)]
    simp only [firstCoeff, g, mul_sub]
    erw [integral_sub ((coord_memLp r).integrable_mul hf2)
      ((coord_memLp r).integrable (by norm_num) |>.mul_const _)]
    rw [integral_mul_const, integral_coord, zero_mul, sub_zero]
    rfl
  have h : 0 ≤ ∫ x, (scalarRemainder g x)^2 ∂γ :=
    integral_nonneg (fun x => sq_nonneg (scalarRemainder g x))
  rw [integral_remainder_sq hg] at h
  simpa only [hc, sub_nonneg, g] using h

/-- A Gram quadratic form written as the sum of the squares of its columns. -/
lemma gram_quadratic (B : Mat) (u : Fin m → ℝ) :
    u ⬝ᵥ ((B * B.transpose) *ᵥ u) = ∑ r, (∑ i, u i * B i r)^2 := by
  rw [← mulVec_mulVec, dotProduct_mulVec, ← vecMul_transpose]
  simp only [dotProduct, vecMul, pow_two, transpose_transpose]

/-- The covariance dominates the Gram matrix of the mean Jacobian. -/
theorem mean_jacobian_gram_le_covariance
    {f : E → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hf2 : Integrable (fun x => f x * ‖x‖^2) volume)
    {F : E → E} (hF : ContDiff ℝ 1 F)
    (hlaw : Measure.map F γ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {J : E → Mat} (hJ : ∀ i j, MemLp (fun x => J x i j) 2 γ)
    (hJF : ∀ x i j, J x i j = (fderiv ℝ F x (PiLp.single 2 j (1 : ℝ))) i) :
    (Matrix.of fun i j => ∫ x, J x i j ∂γ) *
        Matrix.transpose (Matrix.of fun i j => ∫ x, J x i j ∂γ) ≤
      densityCovariance f (∫ x, f x • x) := by
  let B : Mat := fun i j => ∫ x, J x i j ∂γ
  apply Matrix.le_iff.mpr
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((densityCovariance_isHermitian f _).sub ?_)
  · intro u
    let L : E →L[ℝ] ℝ := ∑ i, u i • EuclideanSpace.proj i
    have hL (x : E) : L x = ∑ i, u i * x i := by simp [L]
    have hFlp := transport_memLp hf0 hf hf2 hF.continuous hlaw
    have hd (r : Fin m) (x : E) :
        fderiv ℝ (fun y => L (F y)) x (PiLp.single 2 r (1 : ℝ)) =
          ∑ i, u i * J x i r := by
      erw [(L.hasFDerivAt.comp x ((hF.differentiable (by simp)) x).hasFDerivAt).fderiv]
      simp only [ContinuousLinearMap.comp_apply, hL, hJF]
    have hi (r : Fin m) :
        (∫ x, fderiv ℝ (fun y => L (F y)) x (PiLp.single 2 r (1 : ℝ)) ∂γ) =
          ∑ i, u i * B i r := by
      simp_rw [hd]
      rw [integral_finsetSum _ (fun i _ =>
        ((hJ i r).integrable (by norm_num)).const_mul (u i))]
      simp only [integral_const_mul, B]
    have hp := mean_derivative_sq_le_variance (f := fun y => L (F y))
      (L.differentiable.comp (hF.differentiable (by simp)))
      (hFlp.continuousLinearMap_comp L)
      (fun r => by simpa only [hd] using memLp_row J hJ u r)
    have hv : (∫ x, (L (F x) - ∫ y, L (F y) ∂γ)^2 ∂γ) =
        u ⬝ᵥ (densityCovariance f (∫ x, f x • x) *ᵥ u) := by
      rw [L.integral_comp_comm (hFlp.integrable (by norm_num)),
        transport_mean hf0 hf hF.continuous hlaw,
        densityCovariance_quadratic hf0 hf hf2]
      simpa only [map_sub, hL, PiLp.sub_apply, Finset.sum_sub_distrib, mul_sub]
        using transport_integral hf0 hf hF.continuous hlaw
          (g := fun x => (L (x - ∫ y, f y • y))^2) (by fun_prop)
    rw [hv] at hp
    simp_rw [hi] at hp
    simpa only [star_trivial, sub_mulVec, dotProduct_sub, gram_quadratic, sub_nonneg,
      B, Matrix.of_apply]
      using hp
  · change (B * B.transpose).IsHermitian
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      (posSemidef_self_mul_conjTranspose B).isHermitian

end Submission.Obl.Root.GaussianCovariance
