import Submission.Obl.Entropy__transport_finite_jacobian_energy.Derivatives

open scoped BigOperators Matrix.Norms.Elementwise ContDiff

namespace Submission.Obl.Entropy__transport_finite_jacobian_energy

variable {m : ℕ}

abbrev space (m : ℕ) := EuclideanSpace ℝ (Fin m)

noncomputable def basisVector (i : Fin m) : space m := PiLp.single 2 i 1

lemma contDiff_gradient {φ : space m → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (gradient φ) :=
  (InnerProductSpace.toDual ℝ (space m)).symm.contDiff.comp
    (hφ.fderiv_right (m := ∞) (by simp))

lemma gradient_entry (φ : space m → ℝ) (i : Fin m) (x : space m) :
    gradient φ x i = directional (basisVector i) φ x := by
  rw [directional, ← inner_gradient_left]
  simp only [basisVector, EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul]

lemma directional_euclidean_entry {T : space m → space m} {x : space m}
    (hT : DifferentiableAt ℝ T x) (i : Fin m) (v : space m) :
    directional v (fun y => T y i) x = (directional v T x) i := by
  have h := (EuclideanSpace.proj i).hasFDerivAt.comp x hT.hasFDerivAt
  exact congrArg (fun D => D v) h.fderiv

lemma jacobian_eq_directional_twice {φ : space m → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {J : space m → Matrix (Fin m) (Fin m) ℝ}
    (hJ : ∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (basisVector j)) i)
    (x : space m) (i j : Fin m) :
    J x i j = directional (basisVector j) (directional (basisVector i) φ) x := by
  rw [hJ]
  change (directional (basisVector j) (gradient φ) x) i = _
  rw [← directional_euclidean_entry ((contDiff_gradient hφ).differentiable (by simp) x)]
  congr 2
  funext y
  exact gradient_entry φ i y

lemma contDiff_jacobian {φ : space m → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {J : space m → Matrix (Fin m) (Fin m) ℝ}
    (hJ : ∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (basisVector j)) i) :
    ContDiff ℝ ∞ J := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  have he : (fun x => J x i j) =
      directional (basisVector j) (directional (basisVector i) φ) :=
    funext fun x => jacobian_eq_directional_twice hφ hJ x i j
  rw [he]
  exact contDiff_directional (contDiff_directional hφ _) _

lemma jacobian_symmetric {φ : space m → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {J : space m → Matrix (Fin m) (Fin m) ℝ}
    (hJ : ∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (basisVector j)) i)
    (x : space m) (i j : Fin m) : J x i j = J x j i := by
  simp_rw [jacobian_eq_directional_twice hφ hJ]
  exact directional_comm hφ _ _ _

lemma jacobian_derivative_symmetric {φ : space m → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {J : space m → Matrix (Fin m) (Fin m) ℝ}
    (hJ : ∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (basisVector j)) i)
    (x : space m) (r i j : Fin m) :
    directional (basisVector r) (fun y => J y i j) x =
      directional (basisVector j) (fun y => J y i r) x := by
  simp_rw [jacobian_eq_directional_twice hφ hJ]
  exact directional_comm (contDiff_directional hφ _) _ _ _

lemma jacobian_derivative_swap {φ : space m → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {J : space m → Matrix (Fin m) (Fin m) ℝ}
    (hJ : ∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (basisVector j)) i)
    (x : space m) (r i j : Fin m) :
    directional (basisVector r) (fun y => J y i j) x =
      directional (basisVector i) (fun y => J y r j) x := by
  simp_rw [jacobian_symmetric hφ hJ _ _ j]
  exact jacobian_derivative_symmetric hφ hJ x r j i

lemma jacobian_second_derivative_swap {φ : space m → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {J : space m → Matrix (Fin m) (Fin m) ℝ}
    (hJ : ∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (basisVector j)) i)
    (x : space m) (r s i j : Fin m) :
    directional (basisVector r) (directional (basisVector s) (fun y => J y i j)) x =
      directional (basisVector i) (directional (basisVector j) (fun y => J y r s)) x := by
  have hc (a b : Fin m) : ContDiff ℝ ∞ (fun y => J y a b) :=
    contDiff_pi.mp (contDiff_pi.mp (contDiff_jacobian hφ hJ) a) b
  calc
    _ = directional (basisVector r)
        (directional (basisVector j) (fun y => J y i s)) x := by
      apply congrArg (fun f : space m → ℝ => directional (basisVector r) f x)
      funext y
      exact jacobian_derivative_symmetric hφ hJ y s i j
    _ = directional (basisVector j)
        (directional (basisVector r) (fun y => J y i s)) x :=
      directional_comm (hc i s) _ _ _
    _ = directional (basisVector j)
        (directional (basisVector i) (fun y => J y r s)) x := by
      apply congrArg (fun f : space m → ℝ => directional (basisVector j) f x)
      funext y
      exact jacobian_derivative_swap hφ hJ y r i s
    _ = _ := directional_comm (hc r s) _ _ _

end Submission.Obl.Entropy__transport_finite_jacobian_energy
