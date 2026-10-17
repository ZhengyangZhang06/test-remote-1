import Submission.Obl.Entropy__equality_cases.Rotation
import Submission.Obl.Entropy__equality_cases.JointDiagonal

namespace Submission.Obl.Entropy__equality_cases

open Matrix

/-- The algebraic part of Section 6: compatible normalized coefficients become signed
coordinate projections after rotating both domain and range. -/
theorem signed_coordinate_coefficients {m : ℕ}
    (X : Fin m → Matrix (Fin m) (Fin m) ℝ)
    (hherm : ∀ r, (X r).IsHermitian)
    (hX : CoefficientSymmetry X)
    (h₂ : ∀ r s t i,
      (X r * X t + X t * X r) i s = (X s * X t + X t * X s) i r)
    (hsq : ∑ r, X r * X r = 1) :
    ∃ U : Matrix (Fin m) (Fin m) ℝ,
      U * U.transpose = 1 ∧ U.transpose * U = 1 ∧
      ∃ σ : Fin m → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧
        ∀ r, rotatedCoefficients X U r = diagonal (Pi.single r (σ r)) := by
  obtain ⟨U, hUU, hUtU, eig, heig⟩ :=
    simultaneous_diagonalization X hherm (coefficients_commute X hX h₂)
  refine ⟨U, hUU, hUtU, ?_⟩
  apply diagonal_coefficients_signs
  · exact rotatedCoefficients_symmetry X hX U
  · intro r i j hij
    simp only [rotatedCoefficients, linearField, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul, heig, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, diagonal_apply_ne _ hij, mul_zero, Finset.sum_const_zero]
  · exact rotatedCoefficients_sum_square X U hUU hUtU hsq

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Mixing the input coordinates mixes the coefficient matrices by the columns. -/
theorem linearField_mulVec (X : ι → Matrix ι ι ℝ) (U : Matrix ι ι ℝ) (x : ι → ℝ) :
    linearField X (U *ᵥ x) = ∑ r, x r • linearField X (fun s => U s r) := by
  simp only [linearField, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum,
    smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [mul_comm]

omit [DecidableEq ι] in
/-- Rotation of the whole field agrees with rotation of its coefficients. -/
theorem rotated_linearField (X : ι → Matrix ι ι ℝ) (U : Matrix ι ι ℝ) (x : ι → ℝ) :
    U.transpose * linearField X (U *ᵥ x) * U =
      linearField (rotatedCoefficients X U) x := by
  rw [linearField_mulVec]
  simp only [linearField, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, rotatedCoefficients]

/-- Signed coordinate coefficients have the expected diagonal linear field. -/
theorem linearField_signed_coordinates (σ x : ι → ℝ) :
    linearField (fun r => diagonal (Pi.single r (σ r))) x =
      diagonal (fun i => σ i * x i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [linearField, Matrix.sum_apply, Matrix.smul_apply, Pi.single_apply, mul_comm]
  · simp [linearField, Matrix.sum_apply, Matrix.smul_apply, hij]

/-- Complete finite-dimensional conclusion for a normalized compatible linear matrix field. -/
theorem signed_coordinate_field {m : ℕ}
    (X : Fin m → Matrix (Fin m) (Fin m) ℝ)
    (hherm : ∀ r, (X r).IsHermitian)
    (hX : CoefficientSymmetry X)
    (h₂ : ∀ r s t i,
      (X r * X t + X t * X r) i s = (X s * X t + X t * X s) i r)
    (hsq : ∑ r, X r * X r = 1) :
    ∃ U : Matrix (Fin m) (Fin m) ℝ,
      U * U.transpose = 1 ∧ U.transpose * U = 1 ∧
      ∃ σ : Fin m → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧
        ∀ x, U.transpose * linearField X (U *ᵥ x) * U =
          diagonal (fun i => σ i * x i) := by
  obtain ⟨U, hUU, hUtU, σ, hσ, hcoeff⟩ :=
    signed_coordinate_coefficients X hherm hX h₂ hsq
  refine ⟨U, hUU, hUtU, σ, hσ, ?_⟩
  intro x
  rw [rotated_linearField, show rotatedCoefficients X U =
    (fun r => diagonal (Pi.single r (σ r))) from funext hcoeff,
    linearField_signed_coordinates]

end Submission.Obl.Entropy__equality_cases
