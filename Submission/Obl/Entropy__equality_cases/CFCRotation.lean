import Mathlib

namespace Submission.Obl.Entropy__equality_cases

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Scalar functional calculus on a diagonal real matrix. -/
theorem cfc_diagonal_real (q : ℝ → ℝ) (a : ι → ℝ) :
    cfc q (diagonal a) = diagonal (q ∘ a) := by
  have hspec (i : ι) : a i ∈ spectrum ℝ (diagonal a) := by
    rw [spectrum_diagonal]
    exact Set.mem_range_self i
  let φ : C(spectrum ℝ (diagonal a), ℝ) →⋆ₐ[ℝ] Matrix ι ι ℝ :=
    { toFun := fun g => diagonal (fun i => g ⟨a i, hspec i⟩)
      map_zero' := by simp
      map_one' := by simp
      map_add' := by intro f g; simp [Matrix.diagonal_add]
      map_mul' := by intro f g; simp [Matrix.diagonal_mul_diagonal]
      commutes' := by intro r; simp [Matrix.algebraMap_eq_diagonal]
      map_star' := by intro g; simp [Matrix.star_eq_conjTranspose] }
  have hc : Continuous φ := by
    change Continuous (fun g : C(spectrum ℝ (diagonal a), ℝ) =>
      diagonal (fun i => g ⟨a i, hspec i⟩))
    fun_prop
  have hφ : cfcHom (Matrix.isHermitian_diagonal a).isSelfAdjoint = φ :=
    cfcHom_eq_of_continuous_of_map_id _ φ hc (by rfl)
  rw [cfc_apply q (diagonal a) (Matrix.isHermitian_diagonal a).isSelfAdjoint
    ((diagonal a).finite_real_spectrum.continuousOn q), hφ]
  rfl

/-- Functional calculus commutes with orthogonal conjugation. -/
theorem cfc_orthogonal_conjugate (q : ℝ → ℝ) {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (U : Matrix ι ι ℝ) (hU : U * U.transpose = 1) :
    U * cfc q A * U.transpose = cfc q (U * A * U.transpose) := by
  let u : Matrix.unitaryGroup ι ℝ := ⟨U, by
    simpa only [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
      using hU⟩
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) u
  have hc : Continuous φ := φ.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
  have hφa : IsSelfAdjoint (φ A) := hA.isSelfAdjoint.map φ
  have h := StarAlgHomClass.map_cfc φ q A
    (A.finite_real_spectrum.continuousOn q) hc hA.isSelfAdjoint hφa
  simpa only [φ, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using h

/-- A diagonalized matrix has diagonalized scalar functional calculus in the same basis. -/
theorem cfc_of_orthogonal_diagonalization (q : ℝ → ℝ)
    {A U : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hU : U.transpose * U = 1) {a : ι → ℝ}
    (hdiag : U.transpose * A * U = diagonal a) :
    U.transpose * cfc q A * U = diagonal (q ∘ a) := by
  have h := cfc_orthogonal_conjugate q hA U.transpose (by simpa using hU)
  simpa only [Matrix.transpose_transpose, hdiag, cfc_diagonal_real] using h

end Submission.Obl.Entropy__equality_cases
