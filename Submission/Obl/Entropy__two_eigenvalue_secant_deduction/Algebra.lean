import Submission.Obl.Entropy__two_eigenvalue_secant_deduction.Basic

namespace Submission.Obl.Entropy__two_eigenvalue_secant_deduction
open Submission.Lib.PairEstimate

lemma ell_pos (a : ℝ) : 0 < ell a := by
  unfold ell row
  split_ifs <;> norm_num

lemma m0_nonneg (a : ℝ) : 0 ≤ m0 a := by
  unfold m0
  split_ifs <;> norm_num

lemma endpoint_le (a c G g Z : ℝ) (hc : Certificate c) :
    H a c G g Z ≤ Q G (g-G/2) + Z^2*
      incrementCost (b c) (l c) (e c) (p c) (ell c) (dk a c) (db a c) (psi a c) := by
  apply endpointCost_le _ _ _ _ _ _ _ _ _ _ _ (ell_pos c)
  intro u v
  have hlocal := hc.2.2.2.2.2.1 u v
  dsimp only [endpointCost, Q, D, E, eta, nu,
    Submission.Lib.EntropyTools.chaosQuadratic] at *
  nlinarith only [hlocal]

lemma diagonal (a G g Z : ℝ) (hc : Certificate a) :
    (H a a G g Z + H a a G g Z)/2 ≤ Q G (g-G/2) + sigma a a*Z^2 := by
  have h := endpoint_le a a G g Z hc
  simpa [dk, db, dd, b, l, psi, incrementCost, sigma, delta] using h

lemma dd_symm (v : ℝ → ℝ) (a c : ℝ) : dd v a c = dd v c a := by
  by_cases h : a = c
  · subst c; rfl
  · simp only [dd, if_neg h, if_neg (Ne.symm h)]
    rw [← neg_sub (v a) (v c), ← neg_sub a c]
    simp only [neg_div, div_neg, neg_neg]

lemma sigma_symm (a c : ℝ) : sigma a c = sigma c a := by
  unfold sigma delta
  rw [min_comm]
  ring

end Submission.Obl.Entropy__two_eigenvalue_secant_deduction
