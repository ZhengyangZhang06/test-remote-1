/-
Adapted from: here:o006
Original matrix functional-calculus derivative proofs by session x0063.
-/

import Submission.Lib.MatrixCFCDifferentiation.CFCDerivative

open scoped BigOperators Matrix.Norms.L2Operator

namespace Submission.Lib.MatrixCFCDifferentiation

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-- The linear derivative of scalar functional calculus on Hermitian matrices. -/
noncomputable def spectralDerivative (hA : A.IsHermitian) (f : ℝ → ℝ) :
    Matrix n n ℝ →L[ℝ] Matrix n n ℝ :=
  ∑ i, ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℝ)
    (spectralProjector hA i) (cfc (dslope f (hA.eigenvalues i)) A)

lemma spectralDerivative_apply (hA : A.IsHermitian) (f : ℝ → ℝ) (H : Matrix n n ℝ) :
    spectralDerivative hA f H = ∑ i, spectralProjector hA i * H *
      cfc (dslope f (hA.eigenvalues i)) A := by
  simp [spectralDerivative, ContinuousLinearMap.mulLeftRight_apply]

lemma eigenbasis_cfc (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary).symm (cfc f A) =
      Matrix.diagonal (fun i => f (hA.eigenvalues i)) := by
  rw [hA.cfc_eq]
  exact (Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary).symm_apply_apply _

/-- The Daleckii--Krein formula, including diagonal entries and repeated eigenvalues. -/
lemma spectralDerivative_eigenbasis (hA : A.IsHermitian) (f : ℝ → ℝ)
    (H : Matrix n n ℝ) (i j : n) :
    (Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary).symm
        (spectralDerivative hA f H) i j =
      dslope f (hA.eigenvalues i) (hA.eigenvalues j) *
        (Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary).symm H i j := by
  rw [spectralDerivative_apply, map_sum]
  simp only [map_mul, spectralProjector, StarAlgEquiv.symm_apply_apply, eigenbasis_cfc,
    Matrix.sum_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp [Pi.single_apply, mul_comm]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma fderiv_cfc (A : E → Matrix n n ℝ) (hA : Continuous A)
    (hAH : ∀ x, (A x).IsHermitian) {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {x : E} (hAx : DifferentiableAt ℝ A x) :
    fderiv ℝ (fun y => cfc f (A y)) x =
      (spectralDerivative (hAH x) f).comp (fderiv ℝ A x) := by
  have h := (hasFDerivAt_cfc hA hAH hf hAx.hasFDerivAt).fderiv
  rw [h]
  ext v
  simp [spectralDerivative]

lemma fderiv_cfc_eigenbasis (A : E → Matrix n n ℝ) (hA : Continuous A)
    (hAH : ∀ x, (A x).IsHermitian) {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {x : E} (hAx : DifferentiableAt ℝ A x) (v : E) (i j : n) :
    (Unitary.conjStarAlgAut ℝ _ (hAH x).eigenvectorUnitary).symm
        (fderiv ℝ (fun y => cfc f (A y)) x v) i j =
      dslope f ((hAH x).eigenvalues i) ((hAH x).eigenvalues j) *
        (Unitary.conjStarAlgAut ℝ _ (hAH x).eigenvectorUnitary).symm
          (fderiv ℝ A x v) i j := by
  rw [fderiv_cfc A hA hAH hf hAx, ContinuousLinearMap.comp_apply]
  exact spectralDerivative_eigenbasis (hAH x) f _ i j

end Submission.Lib.MatrixCFCDifferentiation
