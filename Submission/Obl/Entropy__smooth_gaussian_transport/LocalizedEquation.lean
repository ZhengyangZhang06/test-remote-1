import Submission.Obl.Entropy__smooth_gaussian_transport.HessianOperators
import Submission.Obl.Entropy__smooth_gaussian_transport.CutoffHessian

open Set

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def localizedRhs {m : ℕ} (χ u f : E m → ℝ)
    (T : E m → (E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ) (x : E m) : ℝ :=
  χ x * f x + u x * (laplacian χ x - T x (iteratedFDeriv ℝ 2 χ x)) +
    (hessianTrace m - T x) (productHessianCross (fderiv ℝ χ x) (fderiv ℝ u x))

/-- Multiplication by a cutoff places the localized equation in the form
required by the global perturbative Schauder estimate. The extra terms use
only the function and its first derivative. -/
theorem localized_laplacian_equation {m : ℕ} {χ u f : E m → ℝ}
    {T : E m → (E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ}
    (hχ : ContDiff ℝ 2 χ) (hu : ContDiff ℝ 2 u)
    (heq : ∀ x, χ x ≠ 0 → laplacian u x = f x + T x (iteratedFDeriv ℝ 2 u x)) (x : E m) :
    laplacian (fun x => χ x * u x) x = localizedRhs χ u f T x +
      T x (iteratedFDeriv ℝ 2 (fun x => χ x * u x) x) := by
  have hh : χ x * laplacian u x = χ x * (f x + T x (iteratedFDeriv ℝ 2 u x)) := by
    by_cases hx : χ x = 0
    · simp only [hx, zero_mul]
    · rw [heq x hx]
  rw [laplacian_eq_hessianTrace (hχ.mul hu), iteratedFDeriv_two_mul hχ hu,
    map_add, map_add, map_smul, map_smul]
  simp only [smul_eq_mul, ← laplacian_eq_hessianTrace hu, ← laplacian_eq_hessianTrace hχ]
  rw [hh]
  simp only [localizedRhs, map_add, map_smul, sub_apply, smul_eq_mul]
  ring

end Submission.Obl.Entropy__smooth_gaussian_transport
