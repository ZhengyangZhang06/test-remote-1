import Submission.Obl.Entropy__gaussian_chaos_resolvent.HermiteBasis

open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__gaussian_chaos_resolvent

private noncomputable abbrev pdf := Submission.Lib.GaussianTransport.normalPDF
private noncomputable abbrev γ : Measure ℝ := gaussianReal 0 1

/-- Differentiation raises the index on the Gaussian-weighted Hermite polynomials. -/
theorem hasDerivAt_hermitePoly_mul_pdf (n : ℕ) (x : ℝ) :
    HasDerivAt (fun x => (hermitePoly n).eval x * pdf x)
      (-(hermitePoly (n+1)).eval x * pdf x) x := by
  convert ((hermitePoly n).hasDerivAt x).mul
    (Submission.Lib.GaussianTransport.hasDerivAt_normalPDF x) using 1 <;> try rfl
  rw [hermitePoly_succ]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
  ring

/-- Gaussian integration by parts for an arbitrary differentiable H1 function. -/
theorem integral_deriv_mul_hermitePoly {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (hf : MemLp f 2 γ) (hf' : MemLp f' 2 γ)
    (n : ℕ) :
    (∫ x, f' x * (hermitePoly n).eval x ∂γ) =
      ∫ x, f x * (hermitePoly (n+1)).eval x ∂γ := by
  have hint (g : ℝ → ℝ) (hg : MemLp g 2 γ) (n : ℕ) :
      Integrable (fun x => g x * (hermitePoly n).eval x * pdf x) :=
    integrable_gaussianReal_iff.mp (hg.integrable_mul (memLp_polynomial_gaussianReal (hermitePoly n)))
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (v := fun x => (hermitePoly n).eval x * pdf x)
    (u' := f') (v' := fun x => -(hermitePoly (n+1)).eval x * pdf x)
    (fun x _ => hderiv x) (fun x _ => hasDerivAt_hermitePoly_mul_pdf n x)
    (by
      convert (hint f hf (n+1)).neg using 1
      ext x; simp; ring)
    (by convert hint f' hf' n using 1; ext x; simp only [Pi.mul_apply]; ring)
    (by convert hint f hf n using 1; ext x; simp only [Pi.mul_apply]; ring)
  have he : (fun x => f x * (-(hermitePoly (n+1)).eval x * pdf x)) =
      fun x => -(f x * (hermitePoly (n+1)).eval x * pdf x) := by ext x; ring
  change (∫ x, f x * (-(hermitePoly (n+1)).eval x * pdf x)) =
    -(∫ x, f' x * ((hermitePoly n).eval x * pdf x)) at h
  rw [he, integral_neg] at h
  simp only [γ, integral_gaussianReal_eq_integral_smul one_ne_zero, smul_eq_mul]
  have he1 : (fun x => gaussianPDFReal 0 1 x * (f' x * (hermitePoly n).eval x)) =
      fun x => f' x * ((hermitePoly n).eval x * pdf x) := by ext x; dsimp [pdf, Submission.Lib.GaussianTransport.normalPDF]; ring
  have he2 : (fun x => gaussianPDFReal 0 1 x * (f x * (hermitePoly (n+1)).eval x)) =
      fun x => f x * (hermitePoly (n+1)).eval x * pdf x := by ext x; dsimp [pdf, Submission.Lib.GaussianTransport.normalPDF]; ring
  rw [he1, he2]
  linarith

theorem sqrt_factorial_succ (n : ℕ) :
    Real.sqrt ((n+1).factorial : ℝ) = Real.sqrt (n+1 : ℝ) * Real.sqrt (n.factorial : ℝ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Real.sqrt_mul (by positivity)]
  norm_cast

theorem integral_deriv_mul_hermiteFunction {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (hf : MemLp f 2 γ) (hf' : MemLp f' 2 γ)
    (n : ℕ) :
    (∫ x, f' x * hermiteFunction n x ∂γ) =
      Real.sqrt (n+1 : ℝ) * ∫ x, f x * hermiteFunction (n+1) x ∂γ := by
  simp only [hermiteFunction, ← mul_div_assoc, integral_div]
  rw [integral_deriv_mul_hermitePoly hderiv hf hf', sqrt_factorial_succ]
  have h : Real.sqrt (n+1 : ℝ) ≠ 0 := by positivity
  field_simp

end Submission.Obl.Entropy__gaussian_chaos_resolvent
