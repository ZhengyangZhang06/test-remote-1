import Submission.Lib.GaussianTransport.GaussianConvexity
import Submission.Lib.PairEstimate.PairAssembly

open scoped ContDiff
open Set

namespace Submission.Obl.Entropy__two_eigenvalue_secant_deduction

open Submission.Lib.GaussianTransport

noncomputable abbrev q := gaussianHazard
noncomputable abbrev k := transportRatio
noncomputable def b : ℝ → ℝ := deriv k
noncomputable def l : ℝ → ℝ := deriv b
noncomputable def f (a : ℝ) := k a * (1 + b a)
noncomputable def p (a : ℝ) := deriv f a - (b a)^2 - (40/3)*(l a)^2
noncomputable def e (a : ℝ) := deriv f a - 2*(b a)^2 - (80/3)*(l a)^2
noncomputable def D (a : ℝ) := (5/17) / p a
noncomputable def L (a : ℝ) := (40/3) * l a
noncomputable def E (a : ℝ) := e a + (3/4)*b a
noncomputable def eta : ℝ := (40/37)*(7/25) + (42/37)*(3/4)
noncomputable def nu : ℝ := (40/37)*(7/25)^2 + (45/37)*(3/4)^2
noncomputable def Q (u v : ℝ) := (43/100)*u^2 + (26/100)*u*v + (68/25)*v^2
noncomputable def row (a : ℝ) : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ :=
  if a < -3 then (0, 9/100, 3/5, (59/200)*(7+a^2), 37/100, 14/25, 18/25, 13/100)
  else if a < -2 then (83/1000, 3/20, 101/100, 43/10, 29/100, 23/50, 18/25, 13/100)
  else if a < -1 then (7/50, 23/100, 119/100, 3, 29/100, 371/1000, 17/25, 13/100)
  else if a < 1/2 then (11/50, 171/500, 119/100, 43/25, 29/100, 199/500, 61/100, 123/1000)
  else if a < 4 then (337/1000, 9/20, 83/100, 87/100, 31/100, 2/5, 1/2, 3/50)
  else (89/200, 1/2, 1/5, 16/25, 8/25, 2/5, 12/25, 11/500)
noncomputable def ell (a : ℝ) := (row a).2.2.2.2.2.2.2
noncomputable def z (a : ℝ) := deriv l a / l a
noncomputable def hstar (a : ℝ) := 1 + 3*b a + k a*z a
noncomputable def chi (a : ℝ) := l a / (q a-a)
noncomputable def logq (a : ℝ) := Real.log (q a)
noncomputable def delta (a c : ℝ) := logq a - logq c
noncomputable def m0 (a : ℝ) : ℝ :=
  if a < -3 then 0 else if a < -2 then 19/100 else if a < -1 then 38/100 else 68/100
noncomputable def sigma (a c : ℝ) :=
  (1 + m0 (min a c)) / 16 * (1 + (delta a c)^2/30 + (delta a c)^4/1680) *
    (delta a c)^2
noncomputable def dd (v : ℝ → ℝ) (a c : ℝ) :=
  if a = c then deriv v c else (v a-v c)/(a-c)
noncomputable def dk (a c : ℝ) := dd k a c - b c
noncomputable def db (a c : ℝ) := dd b a c - l c
noncomputable def psi (a c : ℝ) :=
  dd f a c - deriv f c - 2*b c*dk a c - (80/3)*l c*db a c
noncomputable def H (a c G g Z : ℝ) :=
  Submission.Lib.PairEstimate.endpointCost (b c) (l c) (e c) (p c)
    G g Z (dk a c) (db a c) (psi a c)

def Certificate (a : ℝ) : Prop :=
  0 < p a ∧ 0 < b a ∧ b a < 1/2 ∧ 0 < l a ∧
  ((row a).1 ≤ b a ∧ b a ≤ (row a).2.1 ∧ L a ≤ (row a).2.2.1 ∧
    D a ≤ (row a).2.2.2.1 ∧ (row a).2.2.2.2.1 ≤ D a*E a ∧
    D a*E a ≤ (row a).2.2.2.2.2.1 ∧ D a*(3/2)*b a ≤ (row a).2.2.2.2.2.2.1) ∧
  (∀ u v : ℝ, ((82/37)*(b a)^2 - eta*b a + nu/4 + (40/3)*(l a)^2)*u^2 +
    2*(nu/2 - eta*b a)*u*v + nu*v^2 + D a*(E a*u+(3/2)*b a*v)^2 +
    ell a*u^2 + (3/4)*v^2 ≤ Q u v) ∧
  (if a < -1 then -(2/25) ≤ z a ∧ z a ≤ 7/10 ∧ chi a ≤ 7/100
    else -(19/40) ≤ z a ∧ z a ≤ 0 ∧ chi a ≤ 97/1000) ∧
  4/5 ≤ hstar a ∧ hstar a ≤ 177/100

theorem smooth_k : ContDiff ℝ ∞ k :=
  contDiff_exponentialTransport.div contDiff_gaussianHazard
    (fun a => (gaussianHazard_pos a).ne')

theorem smooth_b : ContDiff ℝ ∞ b := (contDiff_infty_iff_deriv.mp smooth_k).2
theorem smooth_l : ContDiff ℝ ∞ l := (contDiff_infty_iff_deriv.mp smooth_b).2
theorem smooth_f : ContDiff ℝ ∞ f := smooth_k.mul (contDiff_const.add smooth_b)

theorem b_eq (a : ℝ) : b a = transportSlope a :=
  (hasDerivAt_transportRatio a).deriv

theorem l_eq (a : ℝ) : l a = transportCurvature a := by
  have hb : b = transportSlope := funext b_eq
  change deriv b a = _
  rw [hb]
  exact (hasDerivAt_transportSlope a).deriv

theorem hasDerivAt_k (a : ℝ) : HasDerivAt k (b a) a :=
  smooth_k.differentiable (by simp) a |>.hasDerivAt

theorem hasDerivAt_b (a : ℝ) : HasDerivAt b (l a) a :=
  smooth_b.differentiable (by simp) a |>.hasDerivAt

theorem deriv_f (a : ℝ) : deriv f a = b a*(1+b a) + k a*l a := by
  exact ((hasDerivAt_k a).mul ((hasDerivAt_b a).const_add 1)).deriv

theorem deriv2_f (a : ℝ) (hl : l a ≠ 0) : deriv (deriv f) a = l a*hstar a := by
  have hf : deriv f = fun a => b a*(1+b a) + k a*l a := funext deriv_f
  rw [hf]
  have hd := (((hasDerivAt_b a).mul ((hasDerivAt_b a).const_add 1)).add
    ((hasDerivAt_k a).mul ((smooth_l.differentiable (by simp) a).hasDerivAt))).deriv
  calc
    _ = l a*(1+b a) + b a*l a + (b a*l a+k a*deriv l a) := hd
    _ = _ := by
      unfold hstar z
      field_simp
      <;> ring

theorem hasDerivAt_logq (a : ℝ) : HasDerivAt logq (gaussianGap a) a := by
  convert (hasDerivAt_gaussianHazard a).log (gaussianHazard_pos a).ne' using 1
  · rfl
  · simp [gaussianGap, mul_div_cancel_left₀, (gaussianHazard_pos a).ne']

theorem smooth_logq : ContDiff ℝ ∞ logq :=
  contDiff_gaussianHazard.log (fun a => (gaussianHazard_pos a).ne')

theorem strictMono_logq : StrictMono logq :=
  strictMono_of_hasDerivAt_pos hasDerivAt_logq gaussianGap_pos

theorem concaveOn_logq : ConcaveOn ℝ univ logq := by
  apply concaveOn_of_deriv2_nonpos convex_univ smooth_logq.continuous.continuousOn
  · exact fun a _ => (hasDerivAt_logq a).differentiableAt.differentiableWithinAt
  · have hd : deriv logq = gaussianGap := funext fun a => (hasDerivAt_logq a).deriv
    rw [hd]
    exact fun a _ => (hasDerivAt_gaussianGap a).differentiableAt.differentiableWithinAt
  · intro a _
    have hd : deriv logq = gaussianGap := funext fun a => (hasDerivAt_logq a).deriv
    change deriv (deriv logq) a ≤ 0
    rw [hd, (hasDerivAt_gaussianGap a).deriv]
    linarith [one_sub_hazard_mul_gap_pos a]

end Submission.Obl.Entropy__two_eigenvalue_secant_deduction
