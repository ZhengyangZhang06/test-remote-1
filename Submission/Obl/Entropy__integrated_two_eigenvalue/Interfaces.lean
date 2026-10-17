import Mathlib
import ChallengeDeps

noncomputable section
namespace Submission.Obl.Entropy__integrated_two_eigenvalue

abbrev q : ℝ → ℝ := fun a => ProbabilityTheory.gaussianPDFReal 0 1 a / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a)
abbrev k : ℝ → ℝ := fun a => -Real.log (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a)) / q a

abbrev scalarCertificate (k q : ℝ → ℝ) : ℝ → Prop :=
let b : ℝ → ℝ := deriv k;
let l : ℝ → ℝ := deriv b;
let f : ℝ → ℝ := fun a => k a * (1 + b a);
let p : ℝ → ℝ := fun a => deriv f a - (b a)^2 - (40/3)*(l a)^2;
let e : ℝ → ℝ := fun a => deriv f a - 2*(b a)^2 - (80/3)*(l a)^2;
let Q : ℝ → ℝ → ℝ := fun u v => (43/100)*u^2 + (26/100)*u*v + (68/25)*v^2;
let D : ℝ → ℝ := fun a => (5/17) / p a;
let L : ℝ → ℝ := fun a => (40/3) * l a;
let E : ℝ → ℝ := fun a => e a + (3/4)*b a;
let eta : ℝ := (40/37)*(7/25) + (42/37)*(3/4);
let nu : ℝ := (40/37)*(7/25)^2 + (45/37)*(3/4)^2;
let row : ℝ → (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) := fun a =>
  if a < -3 then (0, 9/100, 3/5, (59/200)*(7+a^2), 37/100, 14/25, 18/25, 13/100)
  else if a < -2 then (83/1000, 3/20, 101/100, 43/10, 29/100, 23/50, 18/25, 13/100)
  else if a < -1 then (7/50, 23/100, 119/100, 3, 29/100, 371/1000, 17/25, 13/100)
  else if a < 1/2 then (11/50, 171/500, 119/100, 43/25, 29/100, 199/500, 61/100, 123/1000)
  else if a < 4 then (337/1000, 9/20, 83/100, 87/100, 31/100, 2/5, 1/2, 3/50)
  else (89/200, 1/2, 1/5, 16/25, 8/25, 2/5, 12/25, 11/500);
fun a : ℝ =>
  let R := row a;
  let z := deriv l a / l a;
  0 < p a ∧ 0 < b a ∧ b a < 1/2 ∧ 0 < l a ∧
  (R.1 ≤ b a ∧ b a ≤ R.2.1 ∧ L a ≤ R.2.2.1 ∧ D a ≤ R.2.2.2.1 ∧
    R.2.2.2.2.1 ≤ D a * E a ∧ D a * E a ≤ R.2.2.2.2.2.1 ∧
    D a * (3/2) * b a ≤ R.2.2.2.2.2.2.1) ∧
  (∀ u v : ℝ,
    ((82/37)*(b a)^2 - eta*b a + nu/4 + (40/3)*(l a)^2)*u^2 +
    2*(nu/2 - eta*b a)*u*v + nu*v^2 +
    D a*(E a*u + (3/2)*b a*v)^2 + R.2.2.2.2.2.2.2*u^2 + (3/4)*v^2 ≤ Q u v) ∧
  (if a < -1 then -(2/25) ≤ z ∧ z ≤ 7/10 ∧ l a / (q a-a) ≤ 7/100
   else -(19/40) ≤ z ∧ z ≤ 0 ∧ l a / (q a-a) ≤ 97/1000) ∧
  4/5 ≤ 1+3*b a+k a*z ∧ 1+3*b a+k a*z ≤ 177/100

abbrev logarithmicGaps (q : ℝ → ℝ) : Prop :=
Real.log (q (-1)) - Real.log (q (-2)) > 81/50 ∧
Real.log (q (-1)) - Real.log (q (-3)) > 4 ∧
Real.log (q 4) - Real.log (q (-2)) > 4 ∧
Real.log (q 4) - Real.log (q (-3)) > 13/2

abbrev pairEstimate (k q : ℝ → ℝ) : Prop :=
let b : ℝ → ℝ := deriv k;
let l : ℝ → ℝ := deriv b;
let f : ℝ → ℝ := fun a => k a * (1 + b a);
let p : ℝ → ℝ := fun a => deriv f a - (b a)^2 - (40/3)*(l a)^2;
let e : ℝ → ℝ := fun a => deriv f a - 2*(b a)^2 - (80/3)*(l a)^2;
let Q : ℝ → ℝ → ℝ := fun u v => (43/100)*u^2 + (26/100)*u*v + (68/25)*v^2;
let delta : ℝ → ℝ → ℝ := fun a c => Real.log (q a) - Real.log (q c);
let sigma : ℝ → ℝ → ℝ := fun a c =>
  (1 + (if min a c < -3 then 0 else if min a c < -2 then 19/100 else if min a c < -1 then 38/100 else 68/100)) / 16 *
  (1 + (delta a c)^2/30 + (delta a c)^4/1680) * (delta a c)^2;
let dd : (ℝ → ℝ) → ℝ → ℝ → ℝ := fun v a c => if a = c then deriv v c else (v a - v c)/(a-c);
let dk : ℝ → ℝ → ℝ := fun a c => dd k a c - b c;
let db : ℝ → ℝ → ℝ := fun a c => dd b a c - l c;
let psi : ℝ → ℝ → ℝ := fun a c => dd f a c - deriv f c - 2*b c*dk a c - (80/3)*l c*db a c;
let H : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun a c G g Z =>
  (40/37)*(G*b c + Z*dk a c - (7/25)*g)^2 +
  (42/37)*(G*b c + Z*dk a c - (3/4)*g)^2 + (27/592)*g^2 +
  (40/3)*(G*l c + Z*db a c)^2 +
  (5/17)*(G*e c + Z*psi a c + (3/2)*g*b c)^2 / p c;
∀ a c G g Z : ℝ, (H a c G g Z + H c a G g Z)/2 ≤ Q G (g-G/2) + sigma a c*Z^2


abbrev positiveWeight (k : ℝ → ℝ) : Prop :=
let b : ℝ → ℝ := deriv k;
let l : ℝ → ℝ := deriv b;
let f : ℝ → ℝ := fun a => k a * (1 + b a);
let p : ℝ → ℝ := fun a => deriv f a - (b a)^2 - (40/3)*(l a)^2;
∀ a : ℝ, 0 < p a

end Submission.Obl.Entropy__integrated_two_eigenvalue
