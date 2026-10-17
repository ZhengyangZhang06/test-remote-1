import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Submission.Obl.Entropy__gaussian_exact_remainder_expansion

/-- Integrating the algebra only requires integrability of the original energies and defects. -/
lemma integrate_expansion {α ρ : Type*} [MeasurableSpace α] [Fintype ρ]
    {μ : Measure α} [IsProbabilityMeasure μ]
    {e u cc r₁ r₂ : α → ℝ} {v : ρ → α → ℝ} (c : ℝ)
    (he : Integrable e μ) (hu : Integrable u μ) (hv : ∀ r, Integrable (v r) μ)
    (h₁ : Integrable r₁ μ) (h₂ : Integrable r₂ μ)
    (hz₁ : ∫ x, r₁ x ∂μ = 0) (hz₂ : ∫ x, r₂ x ∂μ = 0)
    (hpoint : ∀ x, e x+u x+∑ r, v r x = c+cc x+r₁ x+(3/2:ℝ)*r₂ x) :
    (∫ x, e x ∂μ)+(∫ x, u x ∂μ)+(∑ r, ∫ x, v r x ∂μ) = c+∫ x, cc x ∂μ := by
  have hvs : Integrable (fun x => ∑ r, v r x) μ := integrable_finsetSum _ fun r _ => hv r
  have hcc : Integrable cc μ := by
    have hh := (((he.add hu).add hvs).sub (integrable_const c)).sub h₁ |>.sub (h₂.const_mul (3/2))
    convert hh using 1
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    linarith [hpoint x]
  have hi := congrArg (fun z : α → ℝ => ∫ x, z x ∂μ) (funext hpoint)
  have heu : Integrable (fun x => e x+u x) μ := he.add hu
  have hcu : Integrable (fun x => c+cc x) μ := (integrable_const c).add hcc
  have hcu1 : Integrable (fun x => c+cc x+r₁ x) μ := hcu.add h₁
  rw [integral_add heu hvs, integral_add he hu,
    integral_finsetSum _ (fun r _ => hv r),
    integral_add hcu1 (h₂.const_mul (3/2)),
    integral_add hcu h₁,
    integral_add (integrable_const c) hcc, integral_const_mul, hz₁, hz₂] at hi
  simpa using hi

end Submission.Obl.Entropy__gaussian_exact_remainder_expansion
