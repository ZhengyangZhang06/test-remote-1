import Mathlib
import ChallengeDeps

open SimplexIsotropic

namespace Submission.Obl.Root

/-- The dimensional constant in the simplex inequality is positive. -/
theorem simplexBound_pos (n : ℕ) : 0 < simplexBound n := by
  unfold simplexBound
  positivity

/-- The form of the dimensional constant produced by the cone determinant calculation. -/
theorem simplexBound_eq_rpow (n : ℕ) (hn : 1 ≤ n) :
    simplexBound n =
      ((n.factorial : ℝ) ^ 2 /
        (((n : ℝ) + 1) ^ (n + 1) * ((n : ℝ) + 2) ^ n)) ^
          ((1 : ℝ) / (2 * n)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hf : (0 : ℝ) ≤ n.factorial := by positivity
  have h1 : 0 ≤ (n : ℝ) + 1 := by positivity
  have h2 : 0 ≤ (n : ℝ) + 2 := by positivity
  rw [Real.div_rpow (sq_nonneg _) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_natCast_mul hf, ← Real.rpow_natCast_mul h1,
    ← Real.rpow_natCast_mul h2]
  unfold simplexBound
  rw [Real.sqrt_eq_rpow]
  congr 2 <;> push_cast <;> field_simp

/-- The last algebraic step of the paper's cone reduction, in both directions. -/
theorem isotropicConstant_le_iff_det_le (n : ℕ) (hn : 1 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (hv : 0 < vol K) (hd : 0 ≤ (covMatrix K).det) :
    isotropicConstant K ≤ simplexBound n ↔
      ((n : ℝ) + 1) ^ (n + 1) * ((n : ℝ) + 2) ^ n * (covMatrix K).det ≤
        (n.factorial : ℝ) ^ 2 * vol K ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hc : 0 < ((n : ℝ) + 1) ^ (n + 1) * ((n : ℝ) + 2) ^ n := by positivity
  rw [isotropicConstant, simplexBound_eq_rpow n hn,
    Real.rpow_le_rpow_iff (div_nonneg hd (sq_nonneg _)) (by positivity) (by positivity)]
  rw [div_le_div_iff₀ (sq_pos_of_pos hv) hc]
  rw [mul_comm (covMatrix K).det]

/-- Equality is also preserved by the last step of the cone reduction. -/
theorem isotropicConstant_eq_iff_det_eq (n : ℕ) (hn : 1 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (hv : 0 < vol K) (hd : 0 ≤ (covMatrix K).det) :
    isotropicConstant K = simplexBound n ↔
      ((n : ℝ) + 1) ^ (n + 1) * ((n : ℝ) + 2) ^ n * (covMatrix K).det =
        (n.factorial : ℝ) ^ 2 * vol K ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hc : 0 < ((n : ℝ) + 1) ^ (n + 1) * ((n : ℝ) + 2) ^ n := by positivity
  rw [isotropicConstant, simplexBound_eq_rpow n hn, le_antisymm_iff,
    Real.rpow_le_rpow_iff (div_nonneg hd (sq_nonneg _)) (by positivity) (by positivity),
    Real.rpow_le_rpow_iff (by positivity) (div_nonneg hd (sq_nonneg _)) (by positivity),
    ← le_antisymm_iff, div_eq_div_iff (ne_of_gt (sq_pos_of_pos hv)) (ne_of_gt hc)]
  rw [mul_comm (covMatrix K).det]

end Submission.Obl.Root
