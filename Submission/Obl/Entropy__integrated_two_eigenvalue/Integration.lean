import Mathlib
import Submission.Lib.EntropyTools.Remainder

open MeasureTheory
open scoped BigOperators

namespace Submission.Obl.Entropy__integrated_two_eigenvalue

open Submission.Lib.EntropyTools

variable {Ω n r : Type*} [MeasurableSpace Ω] [Fintype n] [Fintype r]
variable {μ : Measure Ω}

lemma integrable_squareSum {F : Ω → Matrix n n ℝ}
    (hF : ∀ i j, MemLp (fun x => F x i j) 2 μ) :
    Integrable (fun x => ∑ i, ∑ j, (F x i j)^2) μ := by
  exact integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => (hF i j).integrable_sq

lemma integrable_chaosQuadratic {F H : Ω → ℝ}
    (hF : MemLp F 2 μ) (hH : MemLp H 2 μ) :
    Integrable (fun x => chaosQuadratic (F x) (H x-F x/2)) μ := by
  have hh : MemLp (fun x => H x-F x/2) 2 μ := by
    simpa only [div_eq_mul_inv, Pi.sub_apply] using! hH.sub (hF.mul_const (2:ℝ)⁻¹)
  simpa only [chaosQuadratic, mul_assoc, Pi.mul_apply] using!
    ((hF.integrable_sq.const_mul (43/100)).add
      ((hF.integrable_mul hh).const_mul (26/100))).add (hh.integrable_sq.const_mul (68/25))

lemma integrable_chaosSum {F H : r → Ω → Matrix n n ℝ}
    (hF : ∀ a i j, MemLp (fun x => F a x i j) 2 μ)
    (hH : ∀ a i j, MemLp (fun x => H a x i j) 2 μ) :
    Integrable (fun x => ∑ a, ∑ i, ∑ j,
      chaosQuadratic (F a x i j) (H a x i j-F a x i j/2)) μ := by
  exact integrable_finsetSum _ fun a _ =>
    integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => integrable_chaosQuadratic (hF a i j) (hH a i j)

/-- Move the five nonnegative residual squares through a finite sum and the integral. -/
lemma integral_budget (F₁ F₂ F₃ F₄ F₅ : r → Ω → Matrix n n ℝ)
    (h₁ : ∀ a i j, MemLp (fun x => F₁ a x i j) 2 μ)
    (h₂ : ∀ a i j, MemLp (fun x => F₂ a x i j) 2 μ)
    (h₃ : ∀ a i j, MemLp (fun x => F₃ a x i j) 2 μ)
    (h₄ : ∀ a i j, MemLp (fun x => F₄ a x i j) 2 μ)
    (h₅ : ∀ a i j, MemLp (fun x => F₅ a x i j) 2 μ) :
    (∑ a, ((40/37)*(∫ x, ∑ i, ∑ j, (F₁ a x i j)^2 ∂μ) +
      (42/37)*(∫ x, ∑ i, ∑ j, (F₂ a x i j)^2 ∂μ) +
      (27/592)*(∫ x, ∑ i, ∑ j, (F₃ a x i j)^2 ∂μ) +
      (40/3)*(∫ x, ∑ i, ∑ j, (F₄ a x i j)^2 ∂μ) +
      (5/17)*(∫ x, ∑ i, ∑ j, (F₅ a x i j)^2 ∂μ))) =
    ∫ x, ∑ a, ((40/37)*(∑ i, ∑ j, (F₁ a x i j)^2) +
      (42/37)*(∑ i, ∑ j, (F₂ a x i j)^2) +
      (27/592)*(∑ i, ∑ j, (F₃ a x i j)^2) +
      (40/3)*(∑ i, ∑ j, (F₄ a x i j)^2) +
      (5/17)*(∑ i, ∑ j, (F₅ a x i j)^2)) ∂μ := by
  have h1 (a : r) := (integrable_squareSum (h₁ a)).const_mul (40/37)
  have h2 (a : r) := (integrable_squareSum (h₂ a)).const_mul (42/37)
  have h3 (a : r) := (integrable_squareSum (h₃ a)).const_mul (27/592)
  have h4 (a : r) := (integrable_squareSum (h₄ a)).const_mul (40/3)
  have h5 (a : r) := (integrable_squareSum (h₅ a)).const_mul (5/17)
  have hI (a : r) := ((((h1 a).add (h2 a)).add (h3 a)).add (h4 a)).add (h5 a)
  erw [integral_finsetSum _ (fun a _ => hI a)]
  apply Finset.sum_congr rfl
  intro a _
  erw [integral_add ((((h1 a).add (h2 a)).add (h3 a)).add (h4 a)) (h5 a),
    integral_add (((h1 a).add (h2 a)).add (h3 a)) (h4 a),
    integral_add ((h1 a).add (h2 a)) (h3 a), integral_add (h1 a) (h2 a)]
  simp only [integral_const_mul]

/-- Once the pointwise estimate and separation integrability are available, integration is monotone. -/
lemma integrated_bound_of_pointwise {B Q S : Ω → ℝ}
    (hB : ∀ x, 0 ≤ B x) (hQ : Integrable Q μ) (hS : Integrable S μ)
    (hbound : ∀ x, B x ≤ Q x + S x) :
    (∫ x, B x ∂μ) ≤ (∫ x, Q x ∂μ) + ∫ x, S x ∂μ := by
  rw [← integral_add hQ hS]
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall hB) (hQ.add hS)
    (Filter.Eventually.of_forall hbound)

end Submission.Obl.Entropy__integrated_two_eigenvalue
