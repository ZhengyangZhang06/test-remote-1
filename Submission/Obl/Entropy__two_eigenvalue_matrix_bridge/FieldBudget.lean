import Submission.Obl.Entropy__two_eigenvalue_matrix_bridge.Fields

open scoped BigOperators
open Matrix

namespace Submission.Obl.Entropy__two_eigenvalue_matrix_bridge

open Submission.Lib.PairEstimate Submission.Lib.EntropyTools

variable {m : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

lemma rotate_right_cfc {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (M : Matrix n n ℝ) (v : ℝ → ℝ) (i j : n) :
    rotate hA.eigenvectorUnitary (M * cfc v A) i j =
      rotate hA.eigenvectorUnitary M i j * v (hA.eigenvalues j) :=
  cfc_right_in_eigenbasis hA M v i j

lemma fieldBudget_le (k : ℝ → ℝ) (hk : ContDiff ℝ (⊤ : ENat) k)
    (sigma : ℝ → ℝ → ℝ) (hp : ∀ a, 0 < scalarP k a)
    (hs : ∀ a c G g Z,
      (endpointCost (deriv k) (deriv (deriv k)) (scalarP k) (scalarE k)
          (deltaK k) (deltaB k) (psi k) a c G g Z +
       endpointCost (deriv k) (deriv (deriv k)) (scalarP k) (scalarE k)
          (deltaK k) (deltaB k) (psi k) c a G g Z)/2 ≤
        chaosQuadratic G (g-G/2) + sigma a c*Z^2)
    (A : EuclideanSpace ℝ (Fin m) → Matrix n n ℝ) (hA : ∀ x, (A x).IsHermitian)
    (X : Fin m → Matrix n n ℝ) (hX : ∀ r, (X r).IsHermitian)
    (g : Fin m → EuclideanSpace ℝ (Fin m) → Matrix n n ℝ)
    (hg : ∀ r x, (g r x).IsHermitian)
    (hC : ∀ (v : ℝ → ℝ), Differentiable ℝ v → ∀ r x i j,
      rotate (hA x).eigenvectorUnitary (entryPartial (fun y => cfc v (A y)) r x) i j =
        dividedDiff v ((hA x).eigenvalues i) ((hA x).eigenvalues j) *
          rotate (hA x).eigenvectorUnitary (entryPartial A r x) i j)
    (r : Fin m) (x : EuclideanSpace ℝ (Fin m)) :
    matrixBudget (scalarP k) (A x) (firstResidual k A X r x)
      (secondResidual k A X r x) (thirdResidual k A X g r x) (g r x) ≤
      (∑ i, ∑ j, chaosQuadratic ((entryPartial A r x - X r) i j)
        (g r x i j - (entryPartial A r x - X r) i j / 2)) +
      ∑ i, ∑ j, sigma ((hA x).eigenvalues i) ((hA x).eigenvalues j) *
        (rotate (hA x).eigenvectorUnitary (entryPartial A r x) i j)^2 := by
  have hb := (contDiff_infty_iff_deriv.mp hk).2
  have hk' := hk.differentiable (by norm_num)
  have hb' := hb.differentiable (by norm_num)
  have hf' := (scalarF_smooth hk).differentiable (by norm_num)
  have hD (i j : n) : rotate (hA x).eigenvectorUnitary (firstResidual k A X r x) i j =
      rotate (hA x).eigenvectorUnitary (entryPartial A r x - X r) i j *
        deriv k ((hA x).eigenvalues j) +
      rotate (hA x).eigenvectorUnitary (entryPartial A r x) i j *
        deltaK k ((hA x).eigenvalues i) ((hA x).eigenvalues j) := by
    simp only [firstResidual, rotate_sub, Matrix.sub_apply, rotate_right_cfc,
      hC k hk', deltaK]
    ring
  have hL (i j : n) : rotate (hA x).eigenvectorUnitary (secondResidual k A X r x) i j =
      rotate (hA x).eigenvectorUnitary (entryPartial A r x - X r) i j *
        deriv (deriv k) ((hA x).eigenvalues j) +
      rotate (hA x).eigenvectorUnitary (entryPartial A r x) i j *
        deltaB k ((hA x).eigenvalues i) ((hA x).eigenvalues j) := by
    simp only [secondResidual, rotate_sub, Matrix.sub_apply, rotate_right_cfc,
      hC (deriv k) hb', deltaB]
    ring
  apply matrixBudget_le (deriv k) (deriv (deriv k)) (scalarP k) (scalarE k)
    (deltaK k) (deltaB k) (psi k) sigma hp hs (hA x) _ _ _ _ _ _
    ((entryPartial_isHermitian A hA r x).sub (hX r)) (hg r x)
    (entryPartial_isHermitian A hA r x) hD hL
  intro i j
  simp only [thirdResidual, rotate_sub, rotate_add, rotate_smul, rotate_nsmul, Matrix.sub_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, rotate_right_cfc,
    hC (scalarF k) hf', hD, hL, scalarE, psi, deltaK, deltaB]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

end Submission.Obl.Entropy__two_eigenvalue_matrix_bridge
