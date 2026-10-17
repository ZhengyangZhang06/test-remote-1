import Mathlib
import Submission.Obl.Entropy__centered_slack_transports.Fields

open MeasureTheory Set Filter
open scoped Topology

namespace Submission.Obl.Entropy__transport_finite_jacobian_energy

/-- A differentiable map with positive quadratic derivative is injective. -/
theorem injective_of_positive_derivative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : E → E} (hT : Differentiable ℝ T)
    (hpos : ∀ x v, v ≠ 0 → 0 < inner ℝ (fderiv ℝ T x v) v) :
    Function.Injective T := by
  intro x y hxy
  by_contra hne
  have hv : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  let f : ℝ → ℝ := fun t => inner ℝ (T (x + t • (y - x))) (y - x)
  have hd (t : ℝ) : HasDerivAt f
      (inner ℝ (fderiv ℝ T (x + t • (y - x)) (y - x)) (y - x)) t := by
    have ha : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) t := by
      simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
    have hb := (hT _).hasFDerivAt.comp_hasDerivAt t ha
    simpa [f, Function.comp_def] using hb.inner ℝ (hasDerivAt_const t (y - x))
  have hm : StrictMono f := strictMono_of_deriv_pos fun t => by
    rw [(hd t).deriv]
    exact hpos _ _ hv
  have hlt := hm (show (0 : ℝ) < 1 by norm_num)
  simpa [f, hxy] using hlt

/-- The determinant of a derivative equals that of its coordinate matrix. -/
theorem det_derivative_from_basis {m : ℕ}
    (T : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (J : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (hJ : ∀ x i j, J x i j = (fderiv ℝ T x (PiLp.single 2 j (1 : ℝ))) i)
    (x : EuclideanSpace ℝ (Fin m)) : (fderiv ℝ T x).det = (J x).det := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin m) ℝ).toBasis]
  congr 1
  ext i j
  simpa [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr] using (hJ x i j).symm

/-- A positive definite coordinate Jacobian gives an injective map. -/
theorem injective_of_posDef_jacobian {m : ℕ}
    {T : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {J : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ}
    (hT : Differentiable ℝ T) (hpos : ∀ x, (J x).PosDef)
    (hJ : ∀ x i j, J x i j = (fderiv ℝ T x (PiLp.single 2 j (1 : ℝ))) i) :
    Function.Injective T := by
  apply injective_of_positive_derivative hT
  intro x v hv
  have he : (fderiv ℝ T x v).ofLp = (J x).mulVec v.ofLp := by
    funext i
    exact Submission.Obl.Entropy__centered_slack_transports.derivative_from_basis T J hJ x v i
  have hv' : v.ofLp ≠ 0 := by
    intro hz
    apply hv
    exact (WithLp.equiv 2 (Fin m → ℝ)).injective hz
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, he, dotProduct_comm]
    using (hpos x).dotProduct_mulVec_pos hv'

end Submission.Obl.Entropy__transport_finite_jacobian_energy
