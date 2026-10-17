import Submission.Obl.Entropy__transport_finite_jacobian_energy.ChainRule
import Submission.Obl.Entropy__transport_finite_jacobian_energy.Algebra

set_option autoImplicit false

open Matrix
open scoped BigOperators Matrix.Norms.Elementwise ContDiff

namespace Submission.Obl.Entropy__transport_finite_jacobian_energy

private lemma one_le_smooth : (1 : WithTop ENat) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma directional_logdet_twice {J : E → Matrix ι ι ℝ}
    (hJ : ContDiff ℝ ∞ J) (hinv : ∀ x, (J x).det ≠ 0) (v w x : E) :
    directional v (directional w (fun y => Real.log (J y).det)) x =
      ((J x)⁻¹ * directional v (directional w J) x).trace -
      ((J x)⁻¹ * directional v J x * (J x)⁻¹ * directional w J x).trace := by
  have he : directional w (fun y => Real.log (J y).det) =
      fun y => ((J y)⁻¹ * directional w J y).trace := by
    funext y
    exact fderiv_logdet_apply (hJ.differentiable (by simp) y) (hinv y) w
  rw [he]
  have hi := (contDiff_matrix_inv hJ hinv).differentiable (by simp) x
  have hw := (contDiff_directional hJ w).differentiable (by simp) x
  erw [directional_matrix_trace (differentiableAt_matrix_mul hi hw),
    directional_matrix_mul hi hw,
    directional_matrix_inv (hJ.of_le one_le_smooth) hinv]
  rw [neg_mul, neg_mul, neg_mul, Matrix.trace_add, Matrix.trace_neg]
  ring

variable {m : ℕ}

/-- First differentiated density equation, in coordinate form. -/
lemma first_logJacobian_equation {φ V U : space m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U)
    {J : space m → Matrix (Fin m) (Fin m) ℝ}
    (hJ : ∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (basisVector j)) i)
    (hinv : ∀ x, (J x).det ≠ 0)
    (hlog : ∀ x, Real.log (J x).det = V (gradient φ x) - U x)
    (hU' : ∀ x i, directional (basisVector i) U x = x i)
    (x : space m) (i : Fin m) :
    ((J x)⁻¹ * directional (basisVector i) J x).trace =
      ∑ r, directional (basisVector r) V (gradient φ x) * J x r i - x i := by
  have hc := contDiff_jacobian hφ hJ
  have hd := fderiv_logdet_apply (hc.differentiable (by simp) x) (hinv x) (basisVector i)
  have he : (fun y => Real.log (J y).det) = fun y => V (gradient φ y) - U y := funext hlog
  rw [he] at hd
  change directional (basisVector i) (fun y => V (gradient φ y) - U y) x = _ at hd
  erw [directional_sub ((hV.differentiable (by simp) _).comp x
    ((contDiff_gradient hφ).differentiable (by simp) x)) (hU.differentiable (by simp) x), hU'] at hd
  change directional (basisVector i) (V ∘ gradient φ) x - x i = _ at hd
  rw [directional_comp_jacobian hJ (hV.differentiable (by simp) _)
    ((contDiff_gradient hφ).differentiable (by simp) x)] at hd
  exact hd.symm

/-- Weighted divergence of the inverse Hessian is the transported target drift. -/
lemma inverse_jacobian_drift {φ V U : space m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U)
    {J : space m → Matrix (Fin m) (Fin m) ℝ}
    (hJ : ∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (basisVector j)) i)
    (hinv : ∀ x, (J x).det ≠ 0)
    (hlog : ∀ x, Real.log (J x).det = V (gradient φ x) - U x)
    (hU' : ∀ x i, directional (basisVector i) U x = x i)
    (x : space m) (r : Fin m) :
    (∑ s, directional (basisVector s) (fun y => (J y)⁻¹ s r) x) -
      (∑ s, x s * (J x)⁻¹ s r) = -directional (basisVector r) V (gradient φ x) := by
  have hc := contDiff_jacobian hφ hJ
  have hi := (contDiff_matrix_inv hc hinv).differentiable (by simp) x
  have hd := hc.differentiable (by simp) x
  have hB (s a b : Fin m) : directional (basisVector s) J x a b =
      directional (basisVector b) J x a s := by
    erw [← directional_matrix_entry hd, ← directional_matrix_entry hd]
    exact jacobian_derivative_symmetric hφ hJ x s a b
  have hcontract := inverse_derivative_contraction ((J x)⁻¹)
    (fun s => directional (basisVector s) J x) hB r
  have hfirst := first_equation_contraction (J x) ((J x)⁻¹)
    (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hinv x)))
    (fun u => directional (basisVector u) V (gradient φ x)) x.ofLp
    (fun b => ((J x)⁻¹ * directional (basisVector b) J x).trace)
    (fun b => first_logJacobian_equation hφ hV hU hJ hinv hlog hU' x b) r
  have hs : (∑ s, directional (basisVector s) (fun y => (J y)⁻¹ s r) x) =
      -(∑ s, ((J x)⁻¹ * directional (basisVector s) J x * (J x)⁻¹) s r) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s _
    erw [directional_matrix_entry hi,
      directional_matrix_inv (hc.of_le one_le_smooth) hinv]
    rw [neg_mul, neg_mul]
    rfl
  rw [hs, hcontract]
  linarith

/-- Fourth-derivative symmetry turns the traced matrix derivative into the
elliptic second derivative of a single Jacobian entry. -/
lemma trace_second_jacobian {φ : space m → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {J : space m → Matrix (Fin m) (Fin m) ℝ}
    (hJ : ∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (basisVector j)) i)
    (P : Matrix (Fin m) (Fin m) ℝ) (x : space m) (i j : Fin m) :
    (P * directional (basisVector j) (directional (basisVector i) J) x).trace =
      ∑ s, ∑ r, P s r * directional (basisVector s)
        (directional (basisVector r) (fun y => J y i j)) x := by
  have hc := contDiff_jacobian hφ hJ
  have he (r s : Fin m) : (fun y => directional (basisVector j) J y r s) =
      directional (basisVector j) (fun y => J y r s) := by
    funext y
    exact (directional_matrix_entry (hc.differentiable (by simp) y) r s _).symm
  rw [directional_comm hc (basisVector j) (basisVector i)]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  erw [← directional_matrix_entry
    ((contDiff_directional hc (basisVector j)).differentiable (by simp) x), he]
  rw [jacobian_second_derivative_swap hφ hJ x i j r s]
  exact directional_comm (contDiff_pi.mp (contDiff_pi.mp hc i) j) _ _ _

/-- The twice-differentiated transport equation, before integration by parts. -/
lemma pointwise_jacobian_equation {φ V U : space m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U)
    {J : space m → Matrix (Fin m) (Fin m) ℝ}
    (hJ : ∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (basisVector j)) i)
    (hinv : ∀ x, (J x).det ≠ 0)
    (hlog : ∀ x, Real.log (J x).det = V (gradient φ x) - U x)
    (hU' : ∀ x i, directional (basisVector i) U x = x i)
    (x : space m) (i j : Fin m) :
    (∑ s, ∑ r, (J x)⁻¹ s r * directional (basisVector s)
        (directional (basisVector r) (fun y => J y i j)) x) -
      (∑ r, directional (basisVector r) V (gradient φ x) *
        directional (basisVector r) (fun y => J y i j) x) =
    -(if i = j then 1 else 0) +
      (J x * Matrix.of (fun u v => fderiv ℝ (fderiv ℝ V) (gradient φ x)
        (basisVector u) (basisVector v)) * J x) i j +
      ((J x)⁻¹ * directional (basisVector i) J x * (J x)⁻¹ *
        directional (basisVector j) J x).trace := by
  have hc := contDiff_jacobian hφ hJ
  have hcomp := hV.comp (contDiff_gradient hφ)
  have he : (fun y => Real.log (J y).det) = fun y => V (gradient φ y) - U y := funext hlog
  have hfirst : directional (basisVector i) (fun y => Real.log (J y).det) =
      fun y => directional (basisVector i) (V ∘ gradient φ) y - y i := by
    rw [he]
    funext y
    erw [directional_sub (hcomp.differentiable (by simp) y) (hU.differentiable (by simp) y), hU']
  have hsecond := directional_logdet_twice hc hinv (basisVector j) (basisVector i) x
  rw [hfirst] at hsecond
  erw [directional_sub ((contDiff_directional hcomp (basisVector i)).differentiable (by simp) x)
    (EuclideanSpace.proj i).differentiableAt, directional_coordinate] at hsecond
  rw [directional_comp_twice hφ hV hJ,
    trace_second_jacobian hφ hJ] at hsecond
  have ht : ((J x)⁻¹ * directional (basisVector j) J x * (J x)⁻¹ *
      directional (basisVector i) J x).trace =
      ((J x)⁻¹ * directional (basisVector i) J x * (J x)⁻¹ *
      directional (basisVector j) J x).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm
      ((J x)⁻¹ * directional (basisVector j) J x)
      ((J x)⁻¹ * directional (basisVector i) J x)
  rw [ht] at hsecond
  linarith

/-- The transport operator is the Gaussian weighted divergence of the inverse
Jacobian applied to the gradient. -/
lemma jacobian_divergence_form {φ V U : space m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U)
    {J : space m → Matrix (Fin m) (Fin m) ℝ}
    (hJ : ∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (basisVector j)) i)
    (hinv : ∀ x, (J x).det ≠ 0)
    (hlog : ∀ x, Real.log (J x).det = V (gradient φ x) - U x)
    (hU' : ∀ x i, directional (basisVector i) U x = x i)
    (x : space m) (i j : Fin m) :
    -(if i = j then 1 else 0) +
      (J x * Matrix.of (fun u v => fderiv ℝ (fderiv ℝ V) (gradient φ x)
        (basisVector u) (basisVector v)) * J x) i j +
      ((J x)⁻¹ * directional (basisVector i) J x * (J x)⁻¹ *
        directional (basisVector j) J x).trace =
    ∑ s, ∑ r, (directional (basisVector s)
      (fun y => (J y)⁻¹ s r * directional (basisVector r) (fun z => J z i j) y) x -
      x s * (J x)⁻¹ s r * directional (basisVector r) (fun y => J y i j) x) := by
  have hc := contDiff_jacobian hφ hJ
  have hi := contDiff_matrix_inv hc hinv
  have he : ContDiff ℝ ∞ (fun y => J y i j) := contDiff_pi.mp (contDiff_pi.mp hc i) j
  have hprod (s r : Fin m) := directional_mul
    ((contDiff_pi.mp (contDiff_pi.mp hi s) r).differentiable (by simp) x)
    ((contDiff_directional he (basisVector r)).differentiable (by simp) x) (basisVector s)
  simp_rw [hprod]
  erw [divergence_sum_algebra]
  simp_rw [inverse_jacobian_drift hφ hV hU hJ hinv hlog hU', neg_mul,
    Finset.sum_neg_distrib, ← sub_eq_add_neg]
  exact (pointwise_jacobian_equation hφ hV hU hJ hinv hlog hU' x i j).symm

end Submission.Obl.Entropy__transport_finite_jacobian_energy
