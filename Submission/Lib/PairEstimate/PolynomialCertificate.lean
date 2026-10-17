/-
Adapted from: here:o017

Original Section 4 and matrix-algebra proofs by session x0043.
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace Submission.Lib.PairEstimate

/-- The degree-four Bernstein lower bound used in Appendix A. -/
lemma quartic_lower_on_unit (c0 c1 c2 c3 c4 L x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (h0 : L ≤ c0) (h1 : L ≤ c0+c1/4)
    (h2 : L ≤ c0+c1/2+c2/6) (h3 : L ≤ c0+3*c1/4+c2/2+c3/4)
    (h4 : L ≤ c0+c1+c2+c3+c4) :
    L ≤ c0+c1*x+c2*x^2+c3*x^3+c4*x^4 := by
  have he : c0+c1*x+c2*x^2+c3*x^3+c4*x^4-L =
    (c0-L)*(1-x)^4 + 4*(c0+c1/4-L)*x*(1-x)^3 +
    6*(c0+c1/2+c2/6-L)*x^2*(1-x)^2 +
    4*(c0+3*c1/4+c2/2+c3/4-L)*x^3*(1-x) +
    (c0+c1+c2+c3+c4-L)*x^4 := by ring
  apply sub_nonneg.mp
  rw [he]
  have h0' := sub_nonneg.mpr h0
  have h1' := sub_nonneg.mpr h1
  have h2' := sub_nonneg.mpr h2
  have h3' := sub_nonneg.mpr h3
  have h4' := sub_nonneg.mpr h4
  have hx' := sub_nonneg.mpr hx1
  positivity

/-- Checking the two signs covers the whole interval [-1,1]. -/
lemma quartic_lower_on_symm (c0 c1 c2 c3 c4 L x : ℝ) (hx : |x| ≤ 1)
    (h0 : L ≤ c0)
    (h1 : ∀ s : ℝ, s = 1 ∨ s = -1 → L ≤ c0+s*c1/4)
    (h2 : ∀ s : ℝ, s = 1 ∨ s = -1 → L ≤ c0+s*c1/2+c2/6)
    (h3 : ∀ s : ℝ, s = 1 ∨ s = -1 → L ≤ c0+3*s*c1/4+c2/2+s*c3/4)
    (h4 : ∀ s : ℝ, s = 1 ∨ s = -1 → L ≤ c0+s*c1+c2+s*c3+c4) :
    L ≤ c0+c1*x+c2*x^2+c3*x^3+c4*x^4 := by
  by_cases hx0 : 0 ≤ x
  · apply quartic_lower_on_unit c0 c1 c2 c3 c4 L x hx0 (le_trans (le_abs_self x) hx) h0
    · simpa using h1 1 (Or.inl rfl)
    · simpa using h2 1 (Or.inl rfl)
    · simpa using h3 1 (Or.inl rfl)
    · simpa using h4 1 (Or.inl rfl)
  · have hb := quartic_lower_on_unit c0 (-c1) c2 (-c3) c4 L (-x)
      (by linarith) (le_trans (neg_le_abs x) hx) h0
      (by simpa using h1 (-1) (Or.inr rfl))
      (by simpa using h2 (-1) (Or.inr rfl))
      (by simpa using h3 (-1) (Or.inr rfl))
      (by simpa using h4 (-1) (Or.inr rfl))
    nlinarith only [hb]

/-- Multiplication of two polynomial enclosures, before truncation. -/
lemma enclosure_mul (f g P Q ep eq : ℝ) (hep : 0 ≤ ep) (heq : 0 ≤ eq)
    (hf : |f-P| ≤ ep) (hg : |g-Q| ≤ eq) :
    |f*g-P*Q| ≤ |P| * eq+|Q| * ep+ep*eq := by
  have he : f*g-P*Q = P*(g-Q)+Q*(f-P)+(f-P)*(g-Q) := by ring
  rw [he]
  calc
    _ ≤ |P*(g-Q)+Q*(f-P)| + |(f-P)*(g-Q)| := abs_add_le _ _
    _ ≤ (|P*(g-Q)|+|Q*(f-P)|) + |(f-P)*(g-Q)| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by
      simp only [abs_mul]
      gcongr

/-- Converting an approximation error to a certified lower bound. -/
lemma lower_of_enclosure {f P e L : ℝ} (he : |f-P| ≤ e) (hP : L+e ≤ P) : L ≤ f := by
  have h := (abs_le.mp he).1
  linarith

end Submission.Lib.PairEstimate
