import Mathlib
import Submission.Obl.Entropy__equality_cases.JointBasis

/-! Algebraic coefficient identities in the rigidity lemma of Section 6. -/

namespace Submission.Obl.Entropy__equality_cases

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The linear symmetric-matrix field determined by its coefficient matrices. -/
def linearField (X : ι → Matrix ι ι ℝ) (x : ι → ℝ) : Matrix ι ι ℝ :=
  ∑ r, x r • X r

/-- The constant compatibility identity is symmetry in the coefficient and column indices. -/
def CoefficientSymmetry (X : ι → Matrix ι ι ℝ) : Prop :=
  ∀ r s i, X r i s = X s i r

omit [DecidableEq ι] in
/-- Coefficient symmetry exchanges the two arguments of the associated bilinear map. -/
theorem linearField_mulVec_comm (X : ι → Matrix ι ι ℝ)
    (hX : CoefficientSymmetry X) (x y : ι → ℝ) :
    linearField X x *ᵥ y = linearField X y *ᵥ x := by
  ext i
  simp only [linearField, mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [hX r s i]
  ring

omit [DecidableEq ι] in
/-- The constant and linear terms of Jacobian compatibility force the coefficients to commute. -/
theorem coefficients_commute (X : ι → Matrix ι ι ℝ)
    (hX : CoefficientSymmetry X)
    (h₂ : ∀ r s t i,
      (X r * X t + X t * X r) i s = (X s * X t + X t * X s) i r) :
    ∀ r s, Commute (X r) (X s) := by
  intro r s
  change X r * X s = X s * X r
  ext i t
  have h := h₂ r s t i
  simp only [Matrix.add_apply, mul_apply] at h ⊢
  simp_rw [hX t s, hX t r, hX r s] at h
  exact add_right_cancel h

omit [Fintype ι] in
/-- Once the coefficients are diagonal, coefficient symmetry leaves a single possible entry. -/
theorem diagonal_coefficients (X : ι → Matrix ι ι ℝ)
    (hX : CoefficientSymmetry X)
    (hdiag : ∀ r i j, i ≠ j → X r i j = 0) (r : ι) :
    X r = diagonal (Pi.single r (X r r r)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hir : i = r
    · subst i
      simp
    · rw [hX r i i, hdiag i i r hir]
      simp [hir]
  · rw [hdiag r i j hij]
    simp [hij]

/-- The square-sum normalization makes the surviving diagonal entries signs. -/
theorem diagonal_coefficients_signs (X : ι → Matrix ι ι ℝ)
    (hX : CoefficientSymmetry X)
    (hdiag : ∀ r i j, i ≠ j → X r i j = 0)
    (hsq : ∑ r, X r * X r = 1) :
    ∃ σ : ι → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧
      ∀ r, X r = diagonal (Pi.single r (σ r)) := by
  refine ⟨fun r => X r r r, ?_, diagonal_coefficients X hX hdiag⟩
  intro i
  have hsq' : (∑ r, diagonal (Pi.single r (X r r r)) *
      diagonal (Pi.single r (X r r r))) = 1 := by
    simpa only [← diagonal_coefficients X hX hdiag] using hsq
  have h := congrArg (fun M : Matrix ι ι ℝ => M i i) hsq'
  simp only [diagonal_mul_diagonal, Matrix.sum_apply, diagonal_apply_eq, one_apply_eq] at h
  have hi : X i i i * X i i i = 1 := by
    simpa [Pi.single_apply] using h
  have hfactor : (X i i i - 1) * (X i i i + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with hpos | hneg
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

end Submission.Obl.Entropy__equality_cases
