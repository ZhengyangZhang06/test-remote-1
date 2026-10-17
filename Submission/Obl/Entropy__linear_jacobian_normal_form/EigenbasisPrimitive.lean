/-
Adapted from: here:o011

Original tree proofs by sessions x0028, x0067, and x0068.
-/

import Mathlib
import Submission.Lib.GaussianTransport.GaussianModel

set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.Entropy__linear_jacobian_normal_form

open Submission.Lib.GaussianTransport

/-- Functional calculus preserves a specified eigenvector; polynomial interpolation suffices
because the matrix spectrum is finite. -/
theorem cfc_toEuclideanLin_eigenvector
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (q : ℝ → ℝ)
    {v : EuclideanSpace ℝ n} {t : ℝ}
    (hv : Matrix.toEuclideanLin A v = t • v) :
    Matrix.toEuclideanLin (cfc q A) v = q t • v := by
  classical
  let s : Finset ℝ := insert t A.finite_real_spectrum.toFinset
  let p : Polynomial ℝ := Lagrange.interpolate s id q
  have hp (z : ℝ) (hz : z ∈ s) : p.eval z = q z :=
    Lagrange.eval_interpolate_at_node q Function.injective_id.injOn hz
  have hcf : cfc q A = Polynomial.aeval A p := by
    rw [← cfc_polynomial p A hA]
    apply cfc_congr
    intro z hz
    exact (hp z (Finset.mem_insert_of_mem (by simpa using hz))).symm
  rw [hcf]
  change (Matrix.toLpLinAlgEquiv 2 (Polynomial.aeval A p)) v = _
  rw [← Polynomial.aeval_algHom_apply (Matrix.toLpLinAlgEquiv 2) A p]
  change (Polynomial.aeval (Matrix.toEuclideanLin A) p) v = _
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul hv, hp t (Finset.mem_insert_self _ _)]

/-- Integrating a Gaussian-hazard Jacobian in an unsigned orthonormal eigenbasis. -/
theorem gaussian_primitive_of_eigenbasis
    {m : ℕ} (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hF : ContDiff ℝ 1 F) (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ x, (A x).IsHermitian)
    (hJ : ∀ x v i, fderiv ℝ F x v i = ∑ j, cfc gaussianHazard (A x) i j * v j)
    (b : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)))
    (hb : ∀ x i, Matrix.toEuclideanLin (A x) (b i) = (b.repr x i) • b i) :
    ∃ a : EuclideanSpace ℝ (Fin m), ∀ x i,
      b.repr (F (b.repr.symm x) - a) i =
        -Real.log (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-x i)) := by
  let ℓ : Fin m → EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ :=
    fun i => (PiLp.proj 2 (fun _ : Fin m => ℝ) i).comp b.repr.toContinuousLinearEquiv.toContinuousLinearMap
  have hℓ (i : Fin m) (x : EuclideanSpace ℝ (Fin m)) : ℓ i x = b.repr x i := rfl
  have hdiff : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hJbasis (x : EuclideanSpace ℝ (Fin m)) (j : Fin m) :
      fderiv ℝ F x (b j) = gaussianHazard (b.repr x j) • b j := by
    have h := cfc_toEuclideanLin_eigenvector (hA x) gaussianHazard (hb x j)
    have hJ' : fderiv ℝ F x (b j) = Matrix.toEuclideanLin (cfc gaussianHazard (A x)) (b j) := by
      ext i
      exact hJ x (b j) i
    exact hJ'.trans h
  have hder (i : Fin m) (x : EuclideanSpace ℝ (Fin m)) :
      (ℓ i).comp (fderiv ℝ F x) = gaussianHazard (ℓ i x) • ℓ i := by
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro j
    change ℓ i (fderiv ℝ F x (b j)) = gaussianHazard (ℓ i x) * ℓ i (b j)
    rw [hJbasis, map_smul]
    simp only [hℓ, OrthonormalBasis.repr_self, PiLp.single_apply, smul_eq_mul]
    split_ifs with hij
    · subst j
      rfl
    · simp
  have hconst (i : Fin m) (x : EuclideanSpace ℝ (Fin m)) :
      ℓ i (F x) - exponentialTransport (ℓ i x) = ℓ i (F 0) - exponentialTransport 0 := by
    have hprim (y : EuclideanSpace ℝ (Fin m)) :
        HasFDerivAt (fun z => exponentialTransport (ℓ i z))
          (gaussianHazard (ℓ i y) • ℓ i) y :=
      (hasDerivAt_exponentialTransport (ℓ i y)).comp_hasFDerivAt y (ℓ i).hasFDerivAt
    have hfun (y : EuclideanSpace ℝ (Fin m)) :
        HasFDerivAt (fun z => ℓ i (F z)) ((ℓ i).comp (fderiv ℝ F y)) y :=
      ((ℓ i).hasFDerivAt (x := F y)).comp y (hdiff y).hasFDerivAt
    have hd (y : EuclideanSpace ℝ (Fin m)) :
        HasFDerivAt (fun z => ℓ i (F z) - exponentialTransport (ℓ i z))
          (0 : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) y := by
      convert! (hfun y).sub (hprim y) using 1
      rw [hder, sub_self]
    have hc := is_const_of_fderiv_eq_zero (fun y => (hd y).differentiableAt)
      (fun y => (hd y).fderiv) x 0
    simpa only [map_zero] using hc
  let w : EuclideanSpace ℝ (Fin m) :=
    WithLp.toLp 2 (fun i => ℓ i (F 0) - exponentialTransport 0)
  refine ⟨b.repr.symm w, ?_⟩
  intro x i
  have h := hconst i (b.repr.symm x)
  simp only [hℓ, b.repr.apply_symm_apply] at h
  change b.repr (F (b.repr.symm x) - b.repr.symm w) i = exponentialTransport (x i)
  rw [map_sub, PiLp.sub_apply, b.repr.apply_symm_apply]
  change b.repr (F (b.repr.symm x)) i - (ℓ i (F 0) - exponentialTransport 0) = _
  rw [hℓ]
  linarith

end Submission.Obl.Entropy__linear_jacobian_normal_form
