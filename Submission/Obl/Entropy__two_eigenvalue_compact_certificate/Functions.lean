import Submission.Lib.GaussianTransport.GaussianSlope

namespace Submission.Obl.Entropy__two_eigenvalue_compact_certificate
open Submission.Lib.GaussianTransport

noncomputable abbrev q : ℝ → ℝ := gaussianHazard
noncomputable abbrev k : ℝ → ℝ := transportRatio
noncomputable def b : ℝ → ℝ := deriv k
noncomputable def l : ℝ → ℝ := deriv b
noncomputable def f (a : ℝ) : ℝ := k a * (1+b a)
noncomputable def p (a : ℝ) : ℝ := deriv f a-(b a)^2-(40/3)*(l a)^2
noncomputable def e (a : ℝ) : ℝ := deriv f a-2*(b a)^2-(80/3)*(l a)^2
noncomputable def D (a : ℝ) : ℝ := (5/17)/p a
noncomputable def L (a : ℝ) : ℝ := (40/3)*l a
noncomputable def E (a : ℝ) : ℝ := e a+(3/4)*b a

theorem b_eq : b = transportSlope := funext fun a => (hasDerivAt_transportRatio a).deriv

theorem l_eq : l = transportCurvature := by
  unfold l
  rw [b_eq]
  exact funext fun a => (hasDerivAt_transportSlope a).deriv

theorem b_formula (a : ℝ) : b a = 1-k a*(q a-a) := by
  rw [b_eq]
  rfl

theorem l_formula (a : ℝ) : l a = k a-q a+a*b a := by
  rw [b_eq, l_eq]
  rfl

theorem deriv_l_formula (a : ℝ) : deriv l a = 2*b a-q a*(q a-a)+a*l a := by
  have hh := ((hasDerivAt_transportRatio a).sub (hasDerivAt_gaussianHazard a)).add
    ((hasDerivAt_id a).mul (hasDerivAt_transportSlope a))
  have hd : HasDerivAt l (2*b a-q a*(q a-a)+a*l a) a := by
    rw [b_eq, l_eq]
    convert! hh using 1
    simp only [id_eq]
    ring
  exact hd.deriv

theorem deriv_f_formula (a : ℝ) : deriv f a = b a*(1+b a)+k a*l a := by
  have hd : HasDerivAt f (b a*(1+b a)+k a*l a) a := by
    unfold f
    rw [b_eq, l_eq]
    convert! (hasDerivAt_transportRatio a).mul
      ((hasDerivAt_transportSlope a).const_add 1) using 1
  exact hd.deriv

theorem p_formula (a : ℝ) : p a = b a+k a*l a-(40/3)*(l a)^2 := by
  unfold p
  rw [deriv_f_formula]
  ring

theorem E_formula (a : ℝ) : E a = p a+b a*(3/4-b a)-(40/3)*(l a)^2 := by
  unfold E e p
  ring

noncomputable def actualValues (a : ℝ) : Nat → ℝ
  | 0 => a
  | 1 => q a
  | 2 => k a
  | 3 => q a-a
  | 4 => b a
  | 5 => l a
  | 6 => deriv l a
  | _ => 0

end Submission.Obl.Entropy__two_eigenvalue_compact_certificate
