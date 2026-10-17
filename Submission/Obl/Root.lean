import Submission.Obl.Root.Reduction
import Submission.Obl.Root.OneDimensional
import Submission.Obl.Entropy__lower_bound
import Submission.Obl.Entropy__equality_cases

open SimplexIsotropic

namespace Submission

open Obl.Root

theorem theorem_1_1_ineq (n : ℕ) (hn : 1 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) :
    isotropicConstant K ≤ simplexBound n := by
  by_cases hdim : n = 1
  · subst n
    exact (simplex_inequality_one hK).1
  obtain ⟨_, _, hnonneg, hupper, hconcave, hint, hmass, hsecond, hent, _, _⟩ :=
    Cone.moments n hn K hK (coneDensity K) rfl
      (densityMean (coneDensity K)) rfl (densityCov (coneDensity K)) rfl
      (densityEntropy (coneDensity K)) rfl
  have hbound := Entropy.lower_bound (n + 1) (by omega) (coneDensity K)
    hnonneg hupper hconcave hint hmass hsecond hent
    (densityMean (coneDensity K)) rfl (densityCov (coneDensity K)) rfl
    (densityEntropy (coneDensity K)) rfl
  exact (isotropicConstant_le_iff_cone_entropy_bound n hn K hK).mpr hbound

theorem theorem_1_1_eq (n : ℕ) (hn : 1 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) :
    isotropicConstant K = simplexBound n ↔ IsSimplex K := by
  by_cases hdim : n = 1
  · subst n
    exact (simplex_inequality_one hK).2
  obtain ⟨_, _, hnonneg, hupper, hconcave, hint, hmass, hsecond, hent, _, _⟩ :=
    Cone.moments n hn K hK (coneDensity K) rfl
      (densityMean (coneDensity K)) rfl (densityCov (coneDensity K)) rfl
      (densityEntropy (coneDensity K)) rfl
  have hequality := Entropy.equality_cases (n + 1) (by omega) (coneDensity K)
    hnonneg hupper hconcave hint hmass hsecond hent
    (densityMean (coneDensity K)) rfl (densityCov (coneDensity K)) rfl
    (densityEntropy (coneDensity K)) rfl
  exact (isotropicConstant_eq_iff_cone_entropy_eq n hn K hK).trans
    (hequality.trans (Cone.simplex_iff_product n hn K hK (coneDensity K) rfl))

end Submission
