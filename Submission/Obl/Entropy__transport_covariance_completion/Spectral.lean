import Mathlib
import Submission.Obl.Entropy__gaussian_hazard_lipschitz.CDF
import Submission.Obl.Entropy__transport_covariance_completion.Assembly

namespace Submission.Obl.Entropy__transport_covariance_completion

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

noncomputable def hazard (a : ℝ) : ℝ :=
  gaussianPDFReal 0 1 a / cdf (gaussianReal 0 1) (-a)

noncomputable def tailLog (a : ℝ) : ℝ :=
  -Real.log (cdf (gaussianReal 0 1) (-a))

noncomputable def ratioK (a : ℝ) : ℝ := tailLog a / hazard a

lemma hazard_pos (a : ℝ) : 0 < hazard a := by
  apply div_pos (gaussianPDFReal_pos 0 1 a one_ne_zero)
  rw [Submission.Obl.Entropy__gaussian_hazard_lipschitz.cdf_eq_mass]
  exact Submission.Obl.Entropy__gaussian_hazard_lipschitz.mass_pos _

lemma log_hazard (a : ℝ) :
    Real.log (hazard a) = -a^2 / 2 - Real.log (2 * Real.pi) / 2 + tailLog a := by
  have hpdf : gaussianPDFReal 0 1 a ≠ 0 := (gaussianPDFReal_pos 0 1 a one_ne_zero).ne'
  have hmass : cdf (gaussianReal 0 1) (-a) ≠ 0 := by
    rw [Submission.Obl.Entropy__gaussian_hazard_lipschitz.cdf_eq_mass]
    exact (Submission.Obl.Entropy__gaussian_hazard_lipschitz.mass_pos _).ne'
  rw [hazard, Real.log_div hpdf hmass]
  change Real.log (Submission.Obl.Entropy__gaussian_hazard_lipschitz.pdf a) - _ = _
  rw [Submission.Obl.Entropy__gaussian_hazard_lipschitz.pdf_formula,
    Real.log_mul (inv_ne_zero (Real.sqrt_pos.mpr (by positivity)).ne') (Real.exp_ne_zero _),
    Real.log_inv, Real.log_exp, Real.log_sqrt (by positivity)]
  dsimp only [tailLog]
  ring

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Spectral trace formula for an arbitrary real function of a symmetric matrix. -/
theorem trace_cfc {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, f (hA.eigenvalues i) := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, trace_diagonal]
  rfl

/-- Spectral determinant formula; the finite spectrum needs no global continuity premise. -/
theorem det_cfc {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).det = ∏ i, f (hA.eigenvalues i) := by
  rw [hA.cfc_eq, IsHermitian.cfc, det_map, det_diagonal]
  rfl

/-- The hazard gives a positive definite transport Jacobian. -/
theorem cfc_hazard_posDef {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (cfc hazard A).PosDef := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  apply Unitary.isUnit_coe.posDef_star_right_conjugate_iff.mpr
  rw [posDef_diagonal_iff]
  exact fun i => hazard_pos _

/-- The scalar entropy identity lifted through the matrix functional calculus. -/
theorem log_det_hazard {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    Real.log (cfc hazard A).det = -(∑ i, ∑ j, (A i j)^2) / 2 -
      (Fintype.card n : ℝ) * Real.log (2 * Real.pi) / 2 + (cfc tailLog A).trace := by
  rw [det_cfc hA, Real.log_prod (fun i _ => (hazard_pos (hA.eigenvalues i)).ne')]
  simp_rw [log_hazard]
  have hs : (∑ i, (hA.eigenvalues i)^2) = ∑ i, ∑ j, (A i j)^2 := by
    rw [← trace_cfc hA (fun x => x^2)]
    have hc : cfc (fun x : ℝ => x^2) A = A * A := by
      have hi : cfc (id : ℝ → ℝ) A = A := cfc_id ℝ A hA
      have hh := cfc_pow (id : ℝ → ℝ) 2 A (by fun_prop) hA
      rw [hi, pow_two] at hh
      exact hh
    rw [hc, trace_square_eq_sum_sq hA]
  rw [trace_cfc hA]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.sum_div, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hs]

end Submission.Obl.Entropy__transport_covariance_completion
