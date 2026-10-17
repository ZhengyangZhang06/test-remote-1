import Submission.Obl.Entropy__normalized_remainder.CFCBound

open scoped BigOperators Matrix.Norms.L2Operator

namespace Submission.Obl.Entropy__normalized_remainder

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Entrywise differentiability gives differentiability in the matrix operator norm. -/
lemma differentiableAt_matrix_of_entries {A : E → Matrix n n ℝ} {x : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) :
    DifferentiableAt ℝ A x := by
  let e : (n → n → ℝ) ≃L[ℝ] Matrix n n ℝ :=
    (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv
  have hpi : DifferentiableAt ℝ (fun y i j => A y i j) x :=
    differentiableAt_pi.2 (fun i => differentiableAt_pi.2 (hA i))
  exact e.differentiableAt.comp x hpi

/-- Evaluation of a matrix Frechet derivative agrees with entrywise differentiation. -/
lemma fderiv_matrix_entry {A : E → Matrix n n ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (i j : n) (v : E) :
    fderiv ℝ (fun y => A y i j) x v = fderiv ℝ A x v i j := by
  let ev : Matrix n n ℝ →L[ℝ] ℝ :=
    { toLinearMap :=
        { toFun := fun M => M i j
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      cont := (continuous_apply j).comp (continuous_apply i) }
  exact congrArg (fun L : E →L[ℝ] ℝ => L v) (ev.hasFDerivAt.comp x hA.hasFDerivAt).fderiv

noncomputable def entryDirectionalDerivative (A : E → Matrix n n ℝ) (x v : E) :
    Matrix n n ℝ := Matrix.of (fun i j => fderiv ℝ (fun y => A y i j) x v)

lemma entryDirectionalDerivative_eq_fderiv {A : E → Matrix n n ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (v : E) :
    entryDirectionalDerivative A x v = fderiv ℝ A x v := by
  ext i j
  exact fderiv_matrix_entry hA i j v

/-- Entrywise version of the CFC derivative, matching the coordinate derivatives
used in the entropy interfaces. -/
lemma entryDirectionalDerivative_cfc (A : E → Matrix n n ℝ)
    (hAc : ∀ i j, Continuous (fun y => A y i j))
    (hAH : ∀ x, (A x).IsHermitian) {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {x : E} (hAd : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) (v : E) :
    entryDirectionalDerivative (fun y => cfc f (A y)) x v =
      spectralDerivative (hAH x) f (entryDirectionalDerivative A x v) := by
  have hAc' : Continuous A := continuous_pi (fun i => continuous_pi (hAc i))
  have hAd' := differentiableAt_matrix_of_entries hAd
  rw [entryDirectionalDerivative_eq_fderiv
    (hasFDerivAt_cfc hAc' hAH hf hAd'.hasFDerivAt).differentiableAt,
    entryDirectionalDerivative_eq_fderiv hAd', fderiv_cfc A hAc' hAH hf hAd',
    ContinuousLinearMap.comp_apply]

lemma entryDirectionalDerivative_cfc_eigenbasis (A : E → Matrix n n ℝ)
    (hAc : ∀ i j, Continuous (fun y => A y i j))
    (hAH : ∀ x, (A x).IsHermitian) {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {x : E} (hAd : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (v : E) (i j : n) :
    ((hAH x).eigenvectorUnitary.val.transpose *
      entryDirectionalDerivative (fun y => cfc f (A y)) x v *
        (hAH x).eigenvectorUnitary.val) i j =
      dslope f ((hAH x).eigenvalues i) ((hAH x).eigenvalues j) *
        ((hAH x).eigenvectorUnitary.val.transpose * entryDirectionalDerivative A x v *
          (hAH x).eigenvectorUnitary.val) i j := by
  rw [entryDirectionalDerivative_cfc A hAc hAH hf hAd]
  simpa only [Unitary.conjStarAlgAut_symm_apply, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      spectralDerivative_eigenbasis (hAH x) f (entryDirectionalDerivative A x v) i j

/-- A uniform scalar derivative bound yields the required entry-square energy bound. -/
lemma entryDirectionalDerivative_cfc_squareSum_le (A : E → Matrix n n ℝ)
    (hAc : ∀ i j, Continuous (fun y => A y i j))
    (hAH : ∀ x, (A x).IsHermitian) {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {x : E} (hAd : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) (v : E)
    {s : Set ℝ} (hs : Convex ℝ s) (hspec : spectrum ℝ (A x) ⊆ s)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ t ∈ s, |deriv f t| ≤ C) :
    matrixSquareSum (entryDirectionalDerivative (fun y => cfc f (A y)) x v) ≤
      C^2 * matrixSquareSum (entryDirectionalDerivative A x v) := by
  rw [entryDirectionalDerivative_cfc A hAc hAH hf hAd]
  exact spectralDerivative_squareSum_le_of_deriv_bound (hAH x) hf _ hs hspec hC hbound

end Submission.Obl.Entropy__normalized_remainder
