/-
Adapted from: here:o017

Original Section 4 and matrix-algebra proofs by session x0043.
-/

import Mathlib
import Submission.Lib.EntropyTools.Remainder

namespace Submission.Lib.PairEstimate

open Submission.Lib.EntropyTools

/-- The five squares in one endpoint of Proposition 3.6. -/
noncomputable def endpointCost (b l e p G g Z x y w : ℝ) : ℝ :=
  (40/37) * (G*b + Z*x - (7/25)*g)^2 +
  (42/37) * (G*b + Z*x - (3/4)*g)^2 + (27/592)*g^2 +
  (40/3)*(G*l + Z*y)^2 + (5/17)/p * (G*e + Z*w + (3/2)*g*b)^2

/-- The increment norm of Section 4, with its coefficients expanded. -/
noncomputable def incrementCost (b l e p ell x y w : ℝ) : ℝ :=
  (82/37)*x^2 + (40/3)*y^2 + (5/17)/p*w^2 +
  (((82/37)*b - ((40/37)*(7/25)+(42/37)*(3/4))/2)*x +
    (40/3)*l*y + (5/17)/p*(e+(3/4)*b)*w)^2/ell +
  (-((40/37)*(7/25)+(42/37)*(3/4))*x + (5/17)/p*(3/2)*b*w)^2/(3/4)

lemma two_mul_le_weighted_sq (c u v : ℝ) (hc : 0 < c) :
    2*u*v ≤ c*u^2+v^2/c := by
  have hs := div_nonneg (sq_nonneg (c*u-v)) hc.le
  have he : (c*u-v)^2/c = c*u^2+v^2/c-2*u*v := by
    field_simp
    <;> ring
  rw [he] at hs
  linarith

/-- Completion against the strict local surplus leaves only the secant increment cost. -/
lemma endpointCost_le (b l e p ell G g Z x y w : ℝ) (hell : 0 < ell)
    (hlocal : ∀ G h : ℝ,
      endpointCost b l e p G (h+G/2) 0 0 0 0 ≤
        chaosQuadratic G h - ell*G^2 - (3/4)*h^2) :
    endpointCost b l e p G g Z x y w ≤
      chaosQuadratic G (g-G/2) + Z^2*incrementCost b l e p ell x y w := by
  let u := ((82/37)*b - ((40/37)*(7/25)+(42/37)*(3/4))/2)*x +
    (40/3)*l*y + (5/17)/p*(e+(3/4)*b)*w
  let v := -((40/37)*(7/25)+(42/37)*(3/4))*x + (5/17)/p*(3/2)*b*w
  have hc := hlocal G (g-G/2)
  have hG := two_mul_le_weighted_sq ell G (Z*u) hell
  have hh := two_mul_le_weighted_sq (3/4) (g-G/2) (Z*v) (by norm_num)
  have he : endpointCost b l e p G g Z x y w =
      endpointCost b l e p G (g-G/2+G/2) 0 0 0 0 +
      Z^2*((82/37)*x^2+(40/3)*y^2+(5/17)/p*w^2) +
      2*G*(Z*u) + 2*(g-G/2)*(Z*v) := by
    dsimp only [endpointCost, u, v]
    ring
  rw [he]
  have hi : Z^2*incrementCost b l e p ell x y w =
      Z^2*((82/37)*x^2+(40/3)*y^2+(5/17)/p*w^2) +
      (Z*u)^2/ell + (Z*v)^2/(3/4) := by
    dsimp only [incrementCost, u, v]
    ring
  rw [hi]
  linarith

end Submission.Lib.PairEstimate
