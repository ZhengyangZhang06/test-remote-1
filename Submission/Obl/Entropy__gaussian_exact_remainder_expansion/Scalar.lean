import Submission.Lib.GaussianTransport.GaussianModel

open scoped ContDiff

namespace Submission.Obl.Entropy__gaussian_exact_remainder_expansion

open Submission.Lib.GaussianTransport

noncomputable abbrev t : ℝ → ℝ := exponentialTransport
noncomputable abbrev k : ℝ → ℝ := transportRatio
noncomputable abbrev b : ℝ → ℝ := deriv k
noncomputable abbrev l : ℝ → ℝ := deriv b
noncomputable def f (a : ℝ) : ℝ := k a * (1 + b a)
noncomputable def p (a : ℝ) : ℝ := deriv f a - (b a)^2 - (40/3) * (l a)^2
noncomputable def h (a : ℝ) : ℝ := f a - (3/2)*k a - (80/3)*(b a-7/25)*l a

lemma b_eq : b = transportSlope :=
  funext fun a => (hasDerivAt_transportRatio a).deriv

lemma l_eq : l = transportCurvature := by
  funext a
  rw [l, b_eq]
  exact (hasDerivAt_transportSlope a).deriv

lemma smooth_k : ContDiff ℝ ∞ k :=
  contDiff_exponentialTransport.div contDiff_gaussianHazard
    (fun a => (gaussianHazard_pos a).ne')

lemma smooth_b : ContDiff ℝ ∞ b := (contDiff_infty_iff_deriv.mp smooth_k).2
lemma smooth_l : ContDiff ℝ ∞ l := (contDiff_infty_iff_deriv.mp smooth_b).2
lemma smooth_f : ContDiff ℝ ∞ f := smooth_k.mul (contDiff_const.add smooth_b)
lemma smooth_p : ContDiff ℝ ∞ p :=
  (((contDiff_infty_iff_deriv.mp smooth_f).2).sub (smooth_b.pow 2)).sub
    (contDiff_const.mul (smooth_l.pow 2))
lemma smooth_h : ContDiff ℝ ∞ h :=
  (smooth_f.sub (contDiff_const.mul smooth_k)).sub
    ((contDiff_const.mul (smooth_b.sub contDiff_const)).mul smooth_l)

lemma deriv_f (a : ℝ) : deriv f a = b a * (1 + b a) + k a * l a := by
  exact ((smooth_k.differentiable (by simp) a).hasDerivAt.mul
    ((smooth_b.differentiable (by simp) a).hasDerivAt.const_add 1)).deriv

/-- The exact scalar multiplier identity underlying the integrated expansion. -/
lemma scalar_multiplier_identity (a : ℝ) :
    2 * t a - (k a)^2 = a * f a - deriv f a + (b a)^2 + 1 := by
  rw [deriv_f, f, b_eq, l_eq]
  have ht := gaussianHazard_mul_transportRatio a
  have hb : transportSlope a = 1 - k a * (gaussianHazard a - a) := rfl
  have hl : transportCurvature a = k a - gaussianHazard a + a * transportSlope a := rfl
  rw [hl]
  dsimp only [k, t] at *
  nlinarith

end Submission.Obl.Entropy__gaussian_exact_remainder_expansion
