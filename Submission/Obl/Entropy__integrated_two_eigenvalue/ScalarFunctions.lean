import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Submission.Obl.Entropy__gaussian_hazard_lipschitz.Hazard

open ProbabilityTheory

namespace Submission.Obl.Entropy__integrated_two_eigenvalue

open Submission.Obl.Entropy__gaussian_hazard_lipschitz

noncomputable def q (a : ℝ) : ℝ := hazard a
noncomputable def t (a : ℝ) : ℝ := -Real.log (mass (-a))
noncomputable def d (a : ℝ) : ℝ := q a - a
noncomputable def k (a : ℝ) : ℝ := t a / q a
noncomputable def b : ℝ → ℝ := deriv k
noncomputable def l : ℝ → ℝ := deriv b
noncomputable def f0 (a : ℝ) : ℝ := k a * (1 + b a)
noncomputable def p (a : ℝ) : ℝ := deriv f0 a - (b a)^2 - (40/3)*(l a)^2

lemma q_eq (a : ℝ) : q a =
    gaussianPDFReal 0 1 a / cdf (gaussianReal 0 1) (-a) := by
  rw [q, hazard, cdf_eq_mass, pdf]

lemma t_eq (a : ℝ) : t a = -Real.log (cdf (gaussianReal 0 1) (-a)) := by
  rw [t, cdf_eq_mass]

lemma q_pos (a : ℝ) : 0 < q a := div_pos (pdf_pos a) (mass_pos (-a))

lemma hasDerivAt_q (a : ℝ) : HasDerivAt q (q a * d a) a :=
  hasDerivAt_hazard a

lemma hasDerivAt_d (a : ℝ) : HasDerivAt d (q a * d a - 1) a :=
  (hasDerivAt_q a).sub (hasDerivAt_id a)

lemma hasDerivAt_t (a : ℝ) : HasDerivAt t (q a) a := by
  have hm : HasDerivAt (fun a => mass (-a)) (-pdf a) a := by
    simpa only [pdf_neg, mul_neg_one] using!
      (hasDerivAt_mass (-a)).comp a (hasDerivAt_neg' a)
  simpa only [q, hazard, neg_div, neg_neg] using!
    (hm.log (mass_pos (-a)).ne').neg

lemma hasDerivAt_k (a : ℝ) : HasDerivAt k (1 - k a * d a) a := by
  convert! (hasDerivAt_t a).div (hasDerivAt_q a) (q_pos a).ne' using 1
  dsimp only [k]
  field_simp [(q_pos a).ne']

lemma b_eq (a : ℝ) : b a = 1 - k a * d a := (hasDerivAt_k a).deriv

lemma hasDerivAt_b (a : ℝ) : HasDerivAt b (k a - q a + a * b a) a := by
  have he : b = fun a => 1 - k a * d a := funext b_eq
  rw [he]
  convert! ((hasDerivAt_k a).mul (hasDerivAt_d a)).const_sub 1 using 1
  dsimp only [d]
  ring

lemma l_eq (a : ℝ) : l a = k a - q a + a * b a := (hasDerivAt_b a).deriv

lemma hasDerivAt_l (a : ℝ) : HasDerivAt l (2 * b a - q a * d a + a * l a) a := by
  have he : l = fun a => k a - q a + a * b a := funext l_eq
  rw [he]
  convert! ((hasDerivAt_k a).sub (hasDerivAt_q a)).add
    ((hasDerivAt_id a).mul (hasDerivAt_b a)) using 1
  simp only [id_eq, one_mul, b_eq]
  ring

lemma hasDerivAt_f0 (a : ℝ) :
    HasDerivAt f0 (b a * (1 + b a) + k a * l a) a := by
  convert! (hasDerivAt_k a).mul ((hasDerivAt_b a).const_add 1) using 1 <;>
    simp only [b_eq, l_eq]

lemma p_eq (a : ℝ) : p a = b a + k a * l a - (40/3)*(l a)^2 := by
  rw [p, (hasDerivAt_f0 a).deriv]
  ring

lemma contDiff_q : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) q := by
  rw [contDiff_infty]
  intro n
  induction n with
  | zero =>
    exact contDiff_zero.mpr
      (continuous_iff_continuousAt.mpr fun a => (hasDerivAt_q a).continuousAt)
  | succ n ih =>
    rw [show ((n+1 : ℕ) : WithTop ENat) = (n : WithTop ENat)+1 by simp,
      contDiff_succ_iff_deriv]
    refine ⟨fun a => (hasDerivAt_q a).differentiableAt, by simp, ?_⟩
    have he : deriv q = fun a => q a * (q a - a) :=
      funext fun a => (hasDerivAt_q a).deriv
    rw [he]
    exact ih.mul (ih.sub contDiff_id)

lemma contDiff_t : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) t := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun a => (hasDerivAt_t a).differentiableAt, ?_⟩
  have he : deriv t = q := funext fun a => (hasDerivAt_t a).deriv
  rw [he]
  exact contDiff_q

lemma contDiff_k : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) k :=
  contDiff_t.div contDiff_q (fun a => (q_pos a).ne')

lemma contDiff_b : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) b := contDiff_k.deriv'

lemma contDiff_l : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) l := contDiff_b.deriv'

lemma contDiff_f0 : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f0 :=
  contDiff_k.mul (contDiff_const.add contDiff_b)

lemma contDiff_p : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) p := by
  have he : p = fun a => b a + k a*l a - (40/3)*(l a)^2 := funext p_eq
  rw [he]
  exact (contDiff_b.add (contDiff_k.mul contDiff_l)).sub
    (contDiff_const.mul (contDiff_l.pow 2))

end Submission.Obl.Entropy__integrated_two_eigenvalue
