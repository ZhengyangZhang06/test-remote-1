import ChallengeDeps
import Submission.Helpers

open SimplexIsotropic

namespace Submission

theorem theorem_1_1_ineq (n : ℕ) (hn : 1 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) :
    isotropicConstant K ≤ simplexBound n := by
  sorry

theorem theorem_1_1_eq (n : ℕ) (hn : 1 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) :
    isotropicConstant K = simplexBound n ↔ IsSimplex K := by
  sorry

end Submission
