import Submission.Obl.Entropy__transport_finite_jacobian_energy.ChainRule

set_option autoImplicit false

open scoped BigOperators ContDiff Matrix.Norms.Elementwise

namespace Submission.Obl.Entropy__transport_finite_jacobian_energy

variable {m : ℕ}

lemma bilinear_apply_basis (L : space m →L[ℝ] space m →L[ℝ] ℝ) (v w : space m) :
    L v w = ∑ i, ∑ j, v i * w j * L (basisVector i) (basisVector j) := by
  rw [clm_apply_basis L v]
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [clm_apply_basis (L (basisVector i)) w, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_eq_mul, mul_assoc]

lemma hessian_posSemidef {V : space m → ℝ} (hV : ContDiff ℝ ∞ V)
    (hpos : ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ V) x v v) (x : space m) :
    (Matrix.of (fun i j => fderiv ℝ (fderiv ℝ V) x (basisVector i) (basisVector j))).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.of_apply]
    rw [← directional_twice hV, ← directional_twice hV]
    exact directional_comm hV _ _ _
  · intro v
    have h := hpos x (WithLp.toLp 2 v)
    rw [bilinear_apply_basis] at h
    simpa only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, star_trivial,
      Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using h

lemma curvature_diag_nonneg {V : space m → ℝ} (hV : ContDiff ℝ ∞ V)
    (hpos : ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (J : Matrix (Fin m) (Fin m) ℝ) (hJ : J.IsHermitian) (x : space m) (i : Fin m) :
    0 ≤ (J * Matrix.of (fun u v => fderiv ℝ (fderiv ℝ V) x
      (basisVector u) (basisVector v)) * J) i i := by
  have h := (hessian_posSemidef hV hpos x).mul_mul_conjTranspose_same J
  rw [hJ.eq] at h
  exact h.diag_nonneg

lemma jacobian_directional_hermitian {φ : space m → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {J : space m → Matrix (Fin m) (Fin m) ℝ}
    (hJ : ∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (basisVector j)) i)
    (x : space m) (r : Fin m) : (directional (basisVector r) J x).IsHermitian := by
  have hc := (contDiff_jacobian hφ hJ).differentiable (by simp) x
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  rw [← directional_matrix_entry hc, ← directional_matrix_entry hc]
  congr 2
  funext y
  exact jacobian_symmetric hφ hJ y j i

end Submission.Obl.Entropy__transport_finite_jacobian_energy
