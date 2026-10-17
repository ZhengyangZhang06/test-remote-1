/- Adapted from: here:o022. Original proofs by session x0047. -/
import Submission.Lib.GaussianHermite.IndexSums

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Lib.GaussianHermite

noncomputable def gaussianCoeff {m : ℕ} (f : GaussianL2 m) (a : Fin m → ℕ) : ℝ :=
  (gaussianHermiteBasis m).repr f a

theorem summable_gaussianCoeff_mul {m : ℕ} (f g : GaussianL2 m) :
    Summable (fun a => gaussianCoeff f a * gaussianCoeff g a) := by
  simpa only [gaussianCoeff, HilbertBasis.repr_apply_apply, real_inner_comm f] using
    (gaussianHermiteBasis m).summable_inner_mul_inner f g

theorem tsum_gaussianCoeff_mul {m : ℕ} (f g : GaussianL2 m) :
    (∑' a, gaussianCoeff f a * gaussianCoeff g a) = inner ℝ f g := by
  simpa only [gaussianCoeff, HilbertBasis.repr_apply_apply, real_inner_comm f] using
    (gaussianHermiteBasis m).tsum_inner_mul_inner f g

theorem summable_gaussianCoeff_sq {m : ℕ} (f : GaussianL2 m) :
    Summable (fun a => (gaussianCoeff f a)^2) := by
  simpa only [pow_two] using summable_gaussianCoeff_mul f f

theorem tsum_gaussianCoeff_sq {m : ℕ} (f : GaussianL2 m) :
    (∑' a, (gaussianCoeff f a)^2) = ‖f‖^2 := by
  simpa only [pow_two, real_inner_self_eq_norm_sq] using tsum_gaussianCoeff_mul f f

theorem gaussianCoeff_toLp {m : ℕ} {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : MemLp f 2 (stdGaussian (EuclideanSpace ℝ (Fin m)))) (a : Fin m → ℕ) :
    gaussianCoeff (hf.toLp f) a =
      ∫ x, f x * hermiteEuclidean a x ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  rw [gaussianCoeff, gaussianHermiteBasis_repr]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  exact congrArg (fun t : ℝ => t * hermiteEuclidean a x) hx

theorem gaussianCoeff_deriv {m : ℕ} (r : Fin m)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : Differentiable ℝ f)
    (hf2 : MemLp f 2 (stdGaussian (EuclideanSpace ℝ (Fin m))))
    (hdf2 : MemLp (fun x => fderiv ℝ f x (PiLp.single 2 r (1 : ℝ))) 2
      (stdGaussian (EuclideanSpace ℝ (Fin m)))) (a : Fin m → ℕ) :
    gaussianCoeff (hdf2.toLp _) a =
      Real.sqrt (a r + 1 : ℝ) * gaussianCoeff (hf2.toLp f) (raiseIndex a r) := by
  simp only [gaussianCoeff_toLp]
  exact integral_coord_deriv_mul_hermite r hf hf2 hdf2 a

theorem norm_toLp_sq {m : ℕ} {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : MemLp f 2 (stdGaussian (EuclideanSpace ℝ (Fin m)))) :
    ‖hf.toLp f‖^2 = ∫ x, (f x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp_real]
  simp only [pow_two]

noncomputable def resolventComponent {m : ℕ} (D : GaussianL2 m) : GaussianL2 m :=
  (gaussianHermiteBasis m).repr.symm ⟨fun a => gaussianCoeff D a / (chaosDegree a + 1 : ℝ), by
    apply (lp.memℓp ((gaussianHermiteBasis m).repr D)).norm.mono
    intro a
    simp only [norm_div, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity : (0:ℝ) < chaosDegree a + 1)]
    apply div_le_self (abs_nonneg _)
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)⟩

@[simp] theorem gaussianCoeff_resolventComponent {m : ℕ} (D : GaussianL2 m) (a : Fin m → ℕ) :
    gaussianCoeff (resolventComponent D) a = gaussianCoeff D a / (chaosDegree a + 1 : ℝ) := by
  simp [gaussianCoeff, resolventComponent]

end Submission.Lib.GaussianHermite
