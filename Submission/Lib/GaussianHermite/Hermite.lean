/- Adapted from: here:o022. Original proofs by session x0047. -/
import Mathlib
import Submission.Lib.GaussianTransport.GaussianTails

open MeasureTheory ProbabilityTheory Polynomial
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Lib.GaussianHermite

noncomputable def hermitePoly (n : ℕ) : Polynomial ℝ :=
  (Polynomial.hermite n).map (Int.castRingHom ℝ)

@[simp] theorem hermitePoly_zero : hermitePoly 0 = 1 := by
  simp [hermitePoly]

@[simp] theorem hermitePoly_one : hermitePoly 1 = X := by
  simp [hermitePoly, Polynomial.hermite_one]

theorem hermitePoly_succ (n : ℕ) :
    hermitePoly (n + 1) = X * hermitePoly n - (hermitePoly n).derivative := by
  simp [hermitePoly, Polynomial.derivative_map]

theorem derivative_hermitePoly_succ (n : ℕ) :
    (hermitePoly (n + 1)).derivative = C (n + 1 : ℝ) * hermitePoly n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hermitePoly_succ (n + 1), derivative_sub, derivative_mul,
      derivative_X, one_mul, ih, derivative_mul, derivative_C, zero_mul, zero_add]
    rw [hermitePoly_succ n]
    push_cast
    simp only [map_add, map_one, map_ofNat]
    ring

private noncomputable abbrev pdf := Submission.Lib.GaussianTransport.normalPDF

/-- Every polynomial has finite absolute Gaussian moments. -/
theorem integrable_polynomial_mul_pdf (p : Polynomial ℝ) :
    Integrable (fun x : ℝ => p.eval x * pdf x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    convert hp.add hq using 1
    · rfl
    · ext x; simp [Polynomial.eval_add, add_mul]
  | monomial n a =>
    simpa only [Polynomial.eval_monomial, mul_assoc] using
      (Submission.Lib.GaussianTransport.integrable_pow_mul_normalPDF n).const_mul a

/-- Gaussian integration by parts for polynomials, with no boundary term. -/
theorem integral_polynomial_derivative (p : Polynomial ℝ) :
    (∫ x, p.derivative.eval x * pdf x) = ∫ x, x * p.eval x * pdf x := by
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => p.eval x) (v := pdf)
    (u' := fun x : ℝ => p.derivative.eval x) (v' := fun x : ℝ => -x * pdf x)
    (fun x _ => p.hasDerivAt x)
    (fun x _ => Submission.Lib.GaussianTransport.hasDerivAt_normalPDF x)
    (by
      convert (integrable_polynomial_mul_pdf (X * p)).neg using 1 <;>
        ext x <;> simp [Polynomial.eval_mul, Polynomial.eval_X] <;> ring)
    (integrable_polynomial_mul_pdf p.derivative)
    (integrable_polynomial_mul_pdf p)
  have he : (fun x : ℝ => p.eval x * (-x * pdf x)) =
      fun x : ℝ => -(x * p.eval x * pdf x) := by ext x; ring
  change (∫ x, p.eval x * (-x * pdf x)) = _ at h
  rw [he, integral_neg] at h
  linarith

/-- The creation recurrence is adjoint to polynomial differentiation. -/
theorem integral_hermitePoly_succ_mul (n : ℕ) (p : Polynomial ℝ) :
    (∫ x, (hermitePoly (n + 1)).eval x * p.eval x * pdf x) =
      ∫ x, (hermitePoly n).eval x * p.derivative.eval x * pdf x := by
  have h := integral_polynomial_derivative (hermitePoly n * p)
  simp only [derivative_mul, eval_add, Polynomial.eval_mul, add_mul] at h
  rw [integral_add
    (by simpa [Polynomial.eval_mul] using integrable_polynomial_mul_pdf ((hermitePoly n).derivative * p))
    (by simpa [Polynomial.eval_mul] using integrable_polynomial_mul_pdf (hermitePoly n * p.derivative))] at h
  rw [hermitePoly_succ]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, sub_mul]
  rw [integral_sub
    (by
      convert integrable_polynomial_mul_pdf (X * hermitePoly n * p) using 1 <;>
        ext x <;> simp [Polynomial.eval_mul, Polynomial.eval_X] <;> ring)
    (by simpa [Polynomial.eval_mul] using integrable_polynomial_mul_pdf ((hermitePoly n).derivative * p))]
  simp only [mul_assoc] at h ⊢
  linarith

/-- Orthogonality and the factorial norm of the probabilists' Hermite polynomials. -/
theorem integral_hermitePoly_mul_pdf (m n : ℕ) :
    (∫ x, (hermitePoly m).eval x * (hermitePoly n).eval x * pdf x) =
      if m = n then (n.factorial : ℝ) else 0 := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero =>
      simpa [pdf, Submission.Lib.GaussianTransport.normalPDF] using
        integral_gaussianPDFReal_eq_one 0 (v := 1) one_ne_zero
    | succ n =>
      have h := integral_hermitePoly_succ_mul n 1
      simpa [mul_comm] using h
  | succ m ih =>
    rw [integral_hermitePoly_succ_mul]
    cases n with
    | zero => simp
    | succ n =>
      rw [derivative_hermitePoly_succ]
      simp only [Polynomial.eval_mul, eval_C]
      have he : (fun x : ℝ => (hermitePoly m).eval x *
          ((n + 1 : ℝ) * (hermitePoly n).eval x) * pdf x) =
          fun x : ℝ => (n + 1 : ℝ) *
            ((hermitePoly m).eval x * (hermitePoly n).eval x * pdf x) := by
        ext x; ring
      rw [he, integral_const_mul, ih]
      by_cases h : m = n
      · simp [h, Nat.factorial_succ]
      · simp [h]

/-- Gaussian integrability is integrability against its positive density. -/
theorem integrable_gaussianReal_iff {f : ℝ → ℝ} :
    Integrable f (gaussianReal 0 1) ↔ Integrable (fun x => f x * pdf x) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall fun x => gaussianPDF_lt_top (μ := 0) (v := 1) (x := x))]
  simp [gaussianPDF, pdf, Submission.Lib.GaussianTransport.normalPDF,
    ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), mul_comm]

theorem integrable_polynomial_gaussianReal (p : Polynomial ℝ) :
    Integrable (fun x : ℝ => p.eval x) (gaussianReal 0 1) :=
  integrable_gaussianReal_iff.mpr (integrable_polynomial_mul_pdf p)

theorem memLp_polynomial_gaussianReal (p : Polynomial ℝ) :
    MemLp (fun x : ℝ => p.eval x) 2 (gaussianReal 0 1) := by
  apply (memLp_two_iff_integrable_sq p.continuous.aestronglyMeasurable).mpr
  convert integrable_polynomial_gaussianReal (p ^ 2) using 1
  ext x
  simp

theorem integral_hermitePoly_mul (m n : ℕ) :
    (∫ x, (hermitePoly m).eval x * (hermitePoly n).eval x ∂gaussianReal 0 1) =
      if m = n then (n.factorial : ℝ) else 0 := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simpa [pdf, Submission.Lib.GaussianTransport.normalPDF,
    mul_comm, mul_left_comm] using integral_hermitePoly_mul_pdf m n

noncomputable def hermiteFunction (n : ℕ) (x : ℝ) : ℝ :=
  (hermitePoly n).eval x / Real.sqrt (n.factorial : ℝ)

theorem memLp_hermiteFunction (n : ℕ) : MemLp (hermiteFunction n) 2 (gaussianReal 0 1) := by
  convert (memLp_polynomial_gaussianReal (hermitePoly n)).const_mul
      (Real.sqrt (n.factorial : ℝ))⁻¹ using 1
  ext x
  simp [hermiteFunction, div_eq_mul_inv, mul_comm]

theorem integral_hermiteFunction_mul (m n : ℕ) :
    (∫ x, hermiteFunction m x * hermiteFunction n x ∂gaussianReal 0 1) =
      if m = n then 1 else 0 := by
  simp only [hermiteFunction, div_mul_div_comm, integral_div,
    integral_hermitePoly_mul]
  split_ifs with h
  · subst m
    rw [← pow_two, Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n.factorial)]
    exact div_self (by positivity)
  · simp

end Submission.Lib.GaussianHermite
