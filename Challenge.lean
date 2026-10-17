import ChallengeDeps

open SimplexIsotropic

/-- Theorem 1.1 (The simplex inequality), inequality part: for every integer `n ≥ 1`,
every convex body `K ⊂ ℝⁿ` satisfies
`L_K ≤ (n!)^{1/n} / ((n+1)^{(n+1)/(2n)} √(n+2))`. -/
theorem theorem_1_1_ineq (n : ℕ) (hn : 1 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) :
    isotropicConstant K ≤ simplexBound n := by
  sorry

/-- Theorem 1.1 (The simplex inequality), equality case: for every integer `n ≥ 1` and every
convex body `K ⊂ ℝⁿ`, equality holds in the simplex inequality if and only if `K` is a
simplex. -/
theorem theorem_1_1_eq (n : ℕ) (hn : 1 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) :
    isotropicConstant K = simplexBound n ↔ IsSimplex K := by
  sorry
