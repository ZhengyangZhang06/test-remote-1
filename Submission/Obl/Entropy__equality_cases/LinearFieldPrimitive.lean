import Submission.Obl.Entropy__equality_cases.SignedField
import Submission.Obl.Entropy__equality_cases.DiagonalPrimitive
import Submission.Obl.Entropy__equality_cases.CFCRotation

namespace Submission.Obl.Entropy__equality_cases

open Matrix

/-- Integrating a compatible linear-field spectral Jacobian after an orthogonal rotation. -/
theorem linear_field_jacobian_primitive {m : ℕ}
    (X : Fin m → Matrix (Fin m) (Fin m) ℝ)
    (hherm : ∀ r, (X r).IsHermitian)
    (hX : CoefficientSymmetry X)
    (h₂ : ∀ r s t i,
      (X r * X t + X t * X r) i s = (X s * X t + X t * X s) i r)
    (hsq : ∑ r, X r * X r = 1)
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (t q : ℝ → ℝ) (ht : ∀ s, HasDerivAt t (q s) s)
    (hF : ∀ x : EuclideanSpace ℝ (Fin m), HasFDerivAt F
      ((cfc q (linearField X x)).toEuclideanLin.toContinuousLinearMap) x) :
    ∃ U : Matrix (Fin m) (Fin m) ℝ,
      U * U.transpose = 1 ∧ U.transpose * U = 1 ∧
      ∃ σ : Fin m → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧
        ∃ w : EuclideanSpace ℝ (Fin m), ∀ x i,
          (U.transpose.toEuclideanLin (F (U.toEuclideanLin x))) i =
            σ i * t (σ i * x i) + w i := by
  obtain ⟨U, hUU, hUtU, σ, hσ, hfield⟩ :=
    signed_coordinate_field X hherm hX h₂ hsq
  let V := U.toEuclideanLin.toContinuousLinearMap
  let W := U.transpose.toEuclideanLin.toContinuousLinearMap
  let G := fun x => W (F (V x))
  have hG (x : EuclideanSpace ℝ (Fin m)) : HasFDerivAt G
      ((diagonal (fun i => q (σ i * x i))).toEuclideanLin.toContinuousLinearMap) x := by
    have h := (W.hasFDerivAt.comp (V x) (hF (V x))).comp x V.hasFDerivAt
    have hHerm : (linearField X (V x)).IsHermitian := by
      unfold linearField
      change (∑ r, (V x) r • X r).conjTranspose = ∑ r, (V x) r • X r
      simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial,
        (hherm _).eq]
    have hd := cfc_of_orthogonal_diagonalization q hHerm hUtU
      (hfield (fun i => x i))
    convert! h using 1
    ext v i
    have heq := congrArg (fun M : Matrix (Fin m) (Fin m) ℝ => (M *ᵥ v) i) hd
    simpa only [V, W, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, Function.comp_def] using heq.symm
  obtain ⟨w, hw⟩ := diagonal_jacobian_primitive G t q ht σ
    (fun i => by rcases hσ i with h | h <;> simp [h]) hG
  exact ⟨U, hUU, hUtU, σ, hσ, w, hw⟩

end Submission.Obl.Entropy__equality_cases
