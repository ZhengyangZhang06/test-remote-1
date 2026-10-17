import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.ActualEnclosures

namespace Submission.Obl.Entropy__absorption_h_square_bound

open Submission.Obl.Entropy__two_eigenvalue_compact_certificate

/-- The polynomial whose nonnegativity is the required square bound. -/
def squareGap : CExpr :=
  let K := CExpr.var 2
  let B := CExpr.var 4
  let L := CExpr.var 5
  let P := (B.add (K.mul L)).sub ((L.mul L).scale (40/3))
  let H := (K.mul (B.sub (.const (1/2)))).sub
    (((B.sub (.const (7/25))).mul L).scale (80/3))
  (P.scale ((67/100)^2)).sub (H.mul H)

theorem squareGap_value (a : ℝ) :
    squareGap.value (actualValues a) = (67/100 : ℝ)^2 * p a -
      (k a * (1+b a) - (3/2)*k a - (80/3)*(b a-7/25)*l a)^2 := by
  rw [p_formula]
  norm_num [squareGap, CExpr.value, actualValues]
  ring

/-- Transfer a rational enclosure certificate to the Gaussian functions. -/
theorem square_bound_of_model (M : Model)
    (hcheck : (squareGap.enclose M.initial).LowerBound 0)
    {x : ℝ} (hx : |x| ≤ 1)
    (hq : |q (M.parameter x)-peval M.hazard x| ≤ 1/10^8)
    (hk : |k (M.parameter x)-peval M.ratio x| ≤ 8/10^7) :
    (k (M.parameter x) * (1+b (M.parameter x)) - (3/2)*k (M.parameter x) -
      (80/3)*(b (M.parameter x)-7/25)*l (M.parameter x))^2 ≤
      (67/100 : ℝ)^2 * p (M.parameter x) := by
  have h := squareGap.nonneg_of_check (M.initial_holds hx hq hk) hx hcheck
  rw [squareGap_value] at h
  linarith only [h]

end Submission.Obl.Entropy__absorption_h_square_bound
