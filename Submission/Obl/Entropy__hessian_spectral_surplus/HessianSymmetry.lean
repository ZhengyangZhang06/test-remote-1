import Mathlib

open scoped BigOperators Topology

namespace Submission.Obl.Entropy__hessian_spectral_surplus

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "E" => EuclideanSpace ℝ n
local notation "∞" => ((⊤ : ENat) : WithTop ENat)

lemma contDiff_gradient {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (gradient φ) := by
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
    (hφ.fderiv_right (by simp))

noncomputable def matrixPartial (F : E → Matrix n n ℝ) (r : n) (x : E) : Matrix n n ℝ :=
  Matrix.of (fun i j => fderiv ℝ (fun y => F y i j) x (PiLp.single 2 r (1 : ℝ)))

lemma matrixPartial_symmetric {F : E → Matrix n n ℝ} (hF : ∀ x, (F x).IsHermitian)
    (r i j : n) (x : E) : matrixPartial F r x i j = matrixPartial F r x j i := by
  have he : (fun y => F y i j) = (fun y => F y j i) := by
    funext y
    simpa using (hF y).apply j i
  simp only [matrixPartial, Matrix.of_apply, he]

lemma jacobian_partial_swap {F : E → E} {J : E → Matrix n n ℝ}
    (hF : ContDiff ℝ 2 F)
    (hJ : ∀ x i j, J x i j = (fderiv ℝ F x (PiLp.single 2 j (1 : ℝ))) i)
    (x : E) (r i j : n) : matrixPartial J r x i j = matrixPartial J j x i r := by
  let f : E → ℝ := fun x => F x i
  have hf : ContDiff ℝ 2 f := by
    exact (PiLp.proj 2 (𝕜 := ℝ) (fun _ : n => ℝ) i).contDiff.comp hF
  have hFd := hF.differentiable (by norm_num)
  have hj (j : n) : (fun y => J y i j) =
      (fun y => fderiv ℝ f y (PiLp.single 2 j (1 : ℝ))) := by
    funext y
    rw [hJ]
    have hp := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp y (hFd y).hasFDerivAt).fderiv
    change fderiv ℝ f y = _ at hp
    rw [hp]
    rfl
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have he (j : n) : fderiv ℝ (fun y => fderiv ℝ f y (PiLp.single 2 j (1 : ℝ))) x =
      (fderiv ℝ (fderiv ℝ f) x).flip (PiLp.single 2 j (1 : ℝ)) := by
    rw [fderiv_clm_apply (hdf x) (differentiableAt_const _)]
    simp
  change fderiv ℝ (fun y => J y i j) x (PiLp.single 2 r (1 : ℝ)) =
    fderiv ℝ (fun y => J y i r) x (PiLp.single 2 j (1 : ℝ))
  rw [hj j, hj r, he j, he r]
  exact hf.contDiffAt.isSymmSndFDerivAt (by simp) _ _

/-- The three indices of a smooth Hessian derivative may be interchanged. -/
lemma hessian_partial_symmetries {φ : E → ℝ} {J : E → Matrix n n ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hJs : ∀ x, (J x).IsHermitian)
    (hJ : ∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (PiLp.single 2 j (1 : ℝ))) i)
    (x : E) :
    (∀ r i j, matrixPartial J r x i j = matrixPartial J r x j i) ∧
    (∀ r i j, matrixPartial J r x i j = matrixPartial J i x r j) := by
  have hF : ContDiff ℝ 2 (gradient φ) := (contDiff_gradient hφ).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ENat) ≤ ⊤))
  refine ⟨fun r i j => matrixPartial_symmetric hJs r i j x, ?_⟩
  intro r i j
  calc
    matrixPartial J r x i j = matrixPartial J j x i r := jacobian_partial_swap hF hJ x r i j
    _ = matrixPartial J j x r i := matrixPartial_symmetric hJs j i r x
    _ = matrixPartial J i x r j := jacobian_partial_swap hF hJ x j r i

end Submission.Obl.Entropy__hessian_spectral_surplus
