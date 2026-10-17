import Mathlib
import Submission.Obl.Entropy__centered_slack_transports.Fields

namespace Submission.Obl.Entropy__transport_covariance_completion

open Matrix
open scoped BigOperators

/-- A differentiable vector field with a positive definite derivative is injective. -/
theorem injective_of_positive_derivative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → E} (hF : Differentiable ℝ F)
    (hpos : ∀ x v, v ≠ 0 → 0 < inner ℝ v (fderiv ℝ F x v)) :
    Function.Injective F := by
  intro x y hxy
  by_contra hne
  let v := y - x
  have hv : v ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  let g := fun t : ℝ => inner ℝ v (F (x + t • v))
  have hd (t : ℝ) : HasDerivAt g (inner ℝ v (fderiv ℝ F (x + t • v) v)) t := by
    have hp : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using (((hasDerivAt_id t).smul_const v).const_add x)
    have hc := (hF (x + t • v)).hasFDerivAt.comp_hasDerivAt t hp
    simpa only [Function.comp_apply, inner_zero_left, add_zero] using
      (hasDerivAt_const t v).inner ℝ hc
  have hm : StrictMono g := strictMono_of_hasDerivAt_pos hd (fun t => hpos _ _ hv)
  have hlt := hm (show (0 : ℝ) < 1 by norm_num)
  simpa [g, v, hxy] using hlt

/-- The coordinate Jacobian supplied by the frozen transport hypothesis is the derivative. -/
theorem derivative_matrix_eq {m : ℕ}
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (J : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (hJ : ∀ x i j, J x i j = (fderiv ℝ F x (PiLp.single 2 j (1 : ℝ))) i)
    (x : EuclideanSpace ℝ (Fin m)) :
    (fderiv ℝ F x).toLinearMap = Matrix.toLpLin 2 2 (J x) := by
  ext v i
  exact Submission.Obl.Entropy__centered_slack_transports.derivative_from_basis F J hJ x v i

/-- Determinants agree under the standard Euclidean basis. -/
theorem derivative_det_eq {m : ℕ}
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (J : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (hJ : ∀ x i j, J x i j = (fderiv ℝ F x (PiLp.single 2 j (1 : ℝ))) i)
    (x : EuclideanSpace ℝ (Fin m)) :
    (fderiv ℝ F x).det = (J x).det := by
  change LinearMap.det (fderiv ℝ F x).toLinearMap = _
  rw [derivative_matrix_eq F J hJ]
  exact LinearMap.det_toLpLin 2 _

/-- Pointwise positive definite Jacobians imply injectivity of the transport. -/
theorem injective_of_posDef_jacobian {m : ℕ}
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hF : Differentiable ℝ F)
    (J : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (hJ : ∀ x i j, J x i j = (fderiv ℝ F x (PiLp.single 2 j (1 : ℝ))) i)
    (hpos : ∀ x, (J x).PosDef) : Function.Injective F := by
  apply injective_of_positive_derivative hF
  intro x v hv
  have hv' : v.ofLp ≠ 0 := by
    intro hz
    apply hv
    exact (WithLp.ofLp_eq_zero 2).mp hz
  have hp := (hpos x).dotProduct_mulVec_pos hv'
  have hd := LinearMap.congr_fun (derivative_matrix_eq F J hJ x) v
  change fderiv ℝ F x v = Matrix.toLpLin 2 2 (J x) v at hd
  rw [EuclideanSpace.inner_eq_star_dotProduct, hd, Matrix.toLpLin_apply]
  simpa only [WithLp.ofLp_toLp, star_trivial, dotProduct_comm] using hp

end Submission.Obl.Entropy__transport_covariance_completion
