import Submission.Obl.Entropy__two_eigenvalue_negative_certificate.Certificate

set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.Entropy__two_eigenvalue_negative_certificate

/-- A readable version of the frozen certificate expression. -/
def RawCertificate (q k : ℝ → ℝ) (a : ℝ) : Prop :=
  let b := deriv k
  let l := deriv b
  let f := fun a => k a * (1 + b a)
  let p := fun a => deriv f a - (b a) ^ 2 - (40 / 3) * (l a) ^ 2
  let e := fun a => deriv f a - 2 * (b a) ^ 2 - (80 / 3) * (l a) ^ 2
  let Q := fun u v : ℝ => (43 / 100) * u ^ 2 + (26 / 100) * u * v + (68 / 25) * v ^ 2
  let D := fun a => (5 / 17) / p a
  let L := fun a => (40 / 3) * l a
  let E := fun a => e a + (3 / 4) * b a
  let row : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ :=
    if a < -3 then (0, 9/100, 3/5, (59/200)*(7+a^2), 37/100, 14/25, 18/25, 13/100)
    else if a < -2 then (83/1000, 3/20, 101/100, 43/10, 29/100, 23/50, 18/25, 13/100)
    else if a < -1 then (7/50, 23/100, 119/100, 3, 29/100, 371/1000, 17/25, 13/100)
    else if a < 1/2 then (11/50, 171/500, 119/100, 43/25, 29/100, 199/500, 61/100, 123/1000)
    else if a < 4 then (337/1000, 9/20, 83/100, 87/100, 31/100, 2/5, 1/2, 3/50)
    else (89/200, 1/2, 1/5, 16/25, 8/25, 2/5, 12/25, 11/500)
  let z := deriv l a / l a
  0 < p a ∧ 0 < b a ∧ b a < 1/2 ∧ 0 < l a ∧
    (row.1 ≤ b a ∧ b a ≤ row.2.1 ∧ L a ≤ row.2.2.1 ∧
      D a ≤ row.2.2.2.1 ∧ row.2.2.2.2.1 ≤ D a * E a ∧
      D a * E a ≤ row.2.2.2.2.2.1 ∧ D a * (3/2) * b a ≤ row.2.2.2.2.2.2.1) ∧
    (∀ u v : ℝ,
      ((82/37)*(b a)^2 - eta*b a + nu/4 + (40/3)*(l a)^2)*u^2 +
      2*(nu/2 - eta*b a)*u*v + nu*v^2 + D a*(E a*u + (3/2)*b a*v)^2 +
      row.2.2.2.2.2.2.2*u^2 + (3/4)*v^2 ≤ Q u v) ∧
    (if a < -1 then -(2/25) ≤ z ∧ z ≤ 7/10 ∧ l a / (q a-a) ≤ 7/100
      else -(19/40) ≤ z ∧ z ≤ 0 ∧ l a / (q a-a) ≤ 97/1000) ∧
    4/5 ≤ 1+3*b a+k a*z ∧ 1+3*b a+k a*z ≤ 177/100

open Submission.Lib.GaussianTransport

lemma raw_negative (a : ℝ) (ha : a ≤ -6) :
    RawCertificate gaussianHazard transportRatio a := by
  have h3 : a < -3 := by linarith
  have h1 : a < -1 := by linarith
  unfold RawCertificate
  simp only [deriv_ratio, deriv_slope, deriv_auxiliary, if_pos h3, if_pos h1]
  have hp : transportSlope a * (1 + transportSlope a) + transportRatio a * transportCurvature a -
      (transportSlope a) ^ 2 - (40 / 3) * (transportCurvature a) ^ 2 =
      pValue (transportRatio a) (transportSlope a) (transportCurvature a) := by
    unfold pValue
    ring
  have he : transportSlope a * (1 + transportSlope a) + transportRatio a * transportCurvature a -
      2 * (transportSlope a) ^ 2 - (80 / 3) * (transportCurvature a) ^ 2 +
      (3 / 4) * transportSlope a =
      eValue (transportRatio a) (transportSlope a) (transportCurvature a) := by
    unfold eValue pValue
    ring
  simp only [hp, he]
  exact negative_certificate ha

end Submission.Obl.Entropy__two_eigenvalue_negative_certificate
