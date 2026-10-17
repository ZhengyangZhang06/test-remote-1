import Mathlib
import ChallengeDeps
import Submission.Obl.Root.ConeReduction
import Submission.Obl.Root.SimplexEquality
import Submission.Obl.Entropy__lower_bound
import Submission.Obl.Entropy__equality_cases
import Submission.Obl.Cone__moments
import Submission.Obl.Cone__simplex_iff_product

open SimplexIsotropic

namespace Submission

open Obl.Root

theorem theorem_1_1_ineq (n : ℕ) (hn : 1 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) :
    isotropicConstant K ≤ simplexBound n := by
  obtain ⟨hv, hd, hnonneg, hupper, hconcave, hint, hmass, hsecond, hent, hH, hC⟩ :=
    Cone.moments n hn K hK (coneDensity K) rfl
      (densityMean (coneDensity K)) rfl (densityCov (coneDensity K)) rfl
      (densityEntropy (coneDensity K)) rfl
  have hbound := Entropy.lower_bound (n + 1) (by omega) (coneDensity K)
    hnonneg hupper hconcave hint hmass hsecond hent
    (densityMean (coneDensity K)) rfl (densityCov (coneDensity K)) rfl
    (densityEntropy (coneDensity K)) rfl
  rw [hH, hC, Nat.cast_add, Nat.cast_one] at hbound
  have ha : 0 < (n.factorial : ℝ) * vol K := by positivity
  have hc : 0 < ((n : ℝ) + 1) ^ (n + 1) * ((n : ℝ) + 2) ^ n *
      (covMatrix K).det := by positivity
  have hlog :
      Real.log (((n : ℝ) + 1) ^ (n + 1) * ((n : ℝ) + 2) ^ n *
        (covMatrix K).det) ≤ Real.log (((n.factorial : ℝ) * vol K) ^ 2) := by
    rw [Real.log_pow]
    norm_num
    linarith
  apply (isotropicConstant_le_iff_det_le n hn K hv hd.le).mpr
  have hdet := (Real.log_le_log_iff hc (sq_pos_of_pos ha)).mp hlog
  simpa only [mul_pow] using hdet

theorem theorem_1_1_eq (n : ℕ) (hn : 1 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) :
    isotropicConstant K = simplexBound n ↔ IsSimplex K := by
  obtain ⟨hv, hd, hnonneg, hupper, hconcave, hint, hmass, hsecond, hent, hH, hC⟩ :=
    Cone.moments n hn K hK (coneDensity K) rfl
      (densityMean (coneDensity K)) rfl (densityCov (coneDensity K)) rfl
      (densityEntropy (coneDensity K)) rfl
  have hequality := Entropy.equality_cases (n + 1) (by omega) (coneDensity K)
    hnonneg hupper hconcave hint hmass hsecond hent
    (densityMean (coneDensity K)) rfl (densityCov (coneDensity K)) rfl
    (densityEntropy (coneDensity K)) rfl
  constructor
  · exact ((isotropicConstant_eq_iff_det_eq n hn K hv hd.le).trans
      ((cone_entropy_eq_iff_det_eq n K hv hd hH hC).symm.trans
        (hequality.trans (Cone.simplex_iff_product n hn K hK (coneDensity K) rfl)))).mp
  · exact simplex_attains_bound n hn K hK

end Submission
