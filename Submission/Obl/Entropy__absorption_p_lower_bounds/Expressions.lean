import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.ActualEnclosures
import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Checks

namespace Submission.Obl.Entropy__absorption_p_lower_bounds

open Submission.Obl.Entropy__two_eigenvalue_compact_certificate

/-- The reserve, expressed in the accepted rational certificate language. -/
def reserveExpr : CExpr :=
  .sub (.add (.var 4) (.mul (.var 2) (.var 5)))
    (.scale (40/3) (.mul (.var 5) (.var 5)))

def negativeExpr : CExpr :=
  .sub (.mul reserveExpr (.add (.const 7) (.mul (.var 0) (.var 0)))) (.const 1)

def positiveExpr (c : ℚ) : CExpr := .sub reserveExpr (.const c)

theorem reserveExpr_value (a : ℝ) : reserveExpr.value (actualValues a) = p a := by
  rw [p_formula]
  simp [reserveExpr, CExpr.value, actualValues, pow_two]

theorem negativeExpr_value (a : ℝ) :
    negativeExpr.value (actualValues a) = p a * (7+a^2)-1 := by
  change reserveExpr.value (actualValues a) * ((7 : ℚ) + a*a) - (1 : ℚ) = _
  rw [reserveExpr_value]
  norm_num [pow_two]

theorem positiveExpr_value (c : ℚ) (a : ℝ) :
    (positiveExpr c).value (actualValues a) = p a-c := by
  change reserveExpr.value (actualValues a) - (c : ℝ) = _
  rw [reserveExpr_value]

theorem negative_of_check (M : Model) {x : ℝ} (hx : |x| ≤ 1)
    (hq : |q (M.parameter x)-peval M.hazard x| ≤ 1/10^8)
    (hk : |k (M.parameter x)-peval M.ratio x| ≤ 8/10^7)
    (hcheck : (negativeExpr.enclose M.initial).LowerBound (1/10^6)) :
    1 / (7+(M.parameter x)^2) ≤ p (M.parameter x) := by
  have hh := hcheck.le (negativeExpr.holds (M.initial_holds hx hq hk) hx) hx
  rw [negativeExpr_value] at hh
  norm_num at hh
  apply (div_le_iff₀ (by positivity : 0 < 7+(M.parameter x)^2)).mpr
  nlinarith

theorem positive_of_check (M : Model) (c : ℚ) {x : ℝ} (hx : |x| ≤ 1)
    (hq : |q (M.parameter x)-peval M.hazard x| ≤ 1/10^8)
    (hk : |k (M.parameter x)-peval M.ratio x| ≤ 8/10^7)
    (hcheck : ((positiveExpr c).enclose M.initial).LowerBound (1/10^6)) :
    (c : ℝ) ≤ p (M.parameter x) := by
  have hh := hcheck.le ((positiveExpr c).holds (M.initial_holds hx hq hk) hx) hx
  rw [positiveExpr_value] at hh
  norm_num at hh
  linarith

end Submission.Obl.Entropy__absorption_p_lower_bounds
