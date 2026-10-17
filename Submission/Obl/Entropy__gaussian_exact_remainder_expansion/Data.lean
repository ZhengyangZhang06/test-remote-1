import Submission.Obl.Entropy__gaussian_exact_remainder_expansion.Scalar
import Submission.Obl.Entropy__gaussian_exact_remainder_expansion.MatrixLp

open MeasureTheory ProbabilityTheory
open scoped BigOperators ContDiff

namespace Submission.Obl.Entropy__gaussian_exact_remainder_expansion

abbrev E (m : ℕ) := EuclideanSpace ℝ (Fin m)
abbrev Mat (m : ℕ) := Matrix (Fin m) (Fin m) ℝ
noncomputable abbrev γ (m : ℕ) := stdGaussian (E m)

variable {m : ℕ}

noncomputable def d (F : E m → Mat m) (r : Fin m) (x : E m) : Mat m :=
  Matrix.of fun i j => fderiv ℝ (fun y => F y i j) x (PiLp.single 2 r (1:ℝ))
noncomputable def c (A : E m → Mat m) (f : ℝ → ℝ) (x : E m) : Mat m := cfc f (A x)
noncomputable def X (A : E m → Mat m) (r : Fin m) : Mat m :=
  Matrix.of fun i j => ∫ x, x r*A x i j ∂γ m
noncomputable def Y (A : E m → Mat m) (x : E m) : Mat m := A x-∑ r, x r • X A r
noncomputable def B (A : E m → Mat m) : Mat m := ∑ r, X A r*X A r
noncomputable def S (A : E m → Mat m) : Mat m := ((37/40:ℝ) • 1+(3/40:ℝ) • B A)⁻¹
noncomputable def T (A : E m → Mat m) : Mat m := S A-1
noncomputable def H (A : E m → Mat m) : Mat m := -T A*(B A-1)
noncomputable def K (A : E m → Mat m) := d (c A k)
noncomputable def D (A : E m → Mat m) (r : Fin m) (x : E m) := K A r x-X A r*c A b x
noncomputable def L (A : E m → Mat m) (r : Fin m) (x : E m) := d (c A b) r x-X A r*c A l x
noncomputable def M (A : E m → Mat m) (g : Fin m → E m → Mat m) (r : Fin m) (x : E m) :=
  d (c A f) r x-X A r*c A (deriv f) x-2 • (D A r x*c A b x)-
  (80/3:ℝ) • (L A r x*c A l x)+(3/2:ℝ) • (g r x*c A b x)
noncomputable def v (A : E m → Mat m) (g : Fin m → E m → Mat m) (r : Fin m) (x : E m) :=
  D A r x-(7/25:ℝ) • g r x
noncomputable def w (A : E m → Mat m) (g : Fin m → E m → Mat m) (r : Fin m) (x : E m) :=
  D A r x-(3/4:ℝ) • g r x
noncomputable def F (A : E m → Mat m) (x : E m) :=
  Y A x*(c A b x-(7/25:ℝ) • 1)+∑ r, X A r*L A r x
noncomputable def u (A : E m → Mat m) (x : E m) := F A x+(B A-1)*c A l x
noncomputable def E2 (A : E m → Mat m) (x : E m) :=
  2 • c A t x-c A k x*c A k x-∑ r, K A r x*K A r x
noncomputable def Core (A : E m → Mat m) (g : Fin m → E m → Mat m) (x : E m) : ℝ :=
  -(H A*c A p x).trace+(T A*(Y A x*c A h x+∑ r, X A r*M A g r x)).trace+
  ((F A x).transpose*S A*F A x).trace+(∑ r, ((v A g r x).transpose*S A*v A g r x).trace)+
  (9/16:ℝ)*(T A*(∑ r, g r x*g r x)).trace
noncomputable def Comm (A : E m → Mat m) (g : Fin m → E m → Mat m) (x : E m) : ℝ :=
  -(T A*c A b x*B A*c A b x-T A*B A*c A b x*c A b x).trace-
  2*((T A*c A b x-c A b x*T A)*(∑ r, X A r*w A g r x)).trace-
  (T A*(∑ r, (w A g r x).transpose*w A g r x)).trace

/-- The frozen functional-calculus interface. -/
def FCRegular (A : E m → Mat m) : Prop := ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f →
  (∀ i j, ContDiff ℝ 1 (fun x => c A f x i j)) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ x i j, |c A f x i j| ≤ C) ∧
  (∀ r, MatrixLp (γ m) 2 (d (c A f) r))

/-- The compact smooth test convention for the Gaussian adjoint. -/
def Div (Q : E m → Mat m) (g : Fin m → E m → Mat m) : Prop :=
  ∀ i j, ∀ z : E m → ℝ, ContDiff ℝ ∞ z → HasCompactSupport z →
    (∫ x, Q x i j*z x ∂γ m) = ∑ r, ∫ x, g r x i j*
      fderiv ℝ z x (PiLp.single 2 r (1:ℝ)) ∂γ m

end Submission.Obl.Entropy__gaussian_exact_remainder_expansion
