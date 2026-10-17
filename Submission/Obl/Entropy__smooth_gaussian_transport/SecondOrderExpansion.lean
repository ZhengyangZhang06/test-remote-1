import Submission.Obl.Entropy__smooth_gaussian_transport.HessianStructure
import Submission.Obl.Entropy__smooth_gaussian_transport.QuadraticApproximation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Differentiability of the gradient gives the quadratic Peano expansion at
that point. Continuity of the Hessian in a neighborhood is not needed. -/
theorem quadratic_expansion_of_hasFDerivAt_gradient {m : ℕ} {u : E m → ℝ}
    (hu : Differentiable ℝ u) {x : E m} {A : E m →L[ℝ] E m}
    (hA : HasFDerivAt (gradient u) A x) :
    (fun h => quadraticError u x (gradient u x) A h) =o[𝓝 0] (fun h : E m => ‖h‖ ^ 2) := by
  have hsym := symmetric_gradient_derivative hu hA
  let R : E m → ℝ := quadraticError u x (gradient u x) A
  let R' : E m → E m →L[ℝ] ℝ := fun h => innerSL ℝ (gradient u (x + h) - gradient u x - A h)
  have hQ (h : E m) : HasFDerivAt (fun z => (1 / 2 : ℝ) * inner ℝ (A z) z)
      (innerSL ℝ (A h)) h := by
    convert! ((A.hasFDerivAt.inner ℝ (hasFDerivAt_id h)).const_mul (1 / 2 : ℝ)) using 1
    ext z
    simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
      fderivInnerCLM_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
      innerSL_apply_apply, id_eq]
    have hcross : inner ℝ (A z) h = inner ℝ (A h) z :=
      (hsym.apply_clm z h).trans (real_inner_comm _ _)
    rw [hcross]
    ring
  have hR (h : E m) : HasFDerivAt R (R' h) h := by
    have hshift : HasFDerivAt (fun z : E m => x + z) (ContinuousLinearMap.id ℝ (E m)) h :=
      (hasFDerivAt_id h).const_add x
    have hcomp := ((hu (x + h)).hasFDerivAt.comp h hshift).sub_const (u x)
    have hlin := (innerSL ℝ (gradient u x)).hasFDerivAt (x := h)
    convert! (hcomp.sub hlin).sub (hQ h) using 1
    ext z
    simp only [R', sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, inner_sub_left, inner_gradient_left]
  have hRsmall : R' =o[𝓝 0] (fun h : E m => ‖h‖ ^ 1) := by
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    have he := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hA).bound hε
    filter_upwards [he] with h hh
    simpa only [R', innerSL_apply_norm, norm_pow, norm_norm, pow_one] using hh
  have ht := (convex_univ : Convex ℝ (univ : Set (E m))).isLittleO_pow_succ
    (x₀ := (0 : E m)) (n := 1) (mem_univ 0)
    (fun h _ => (hR h).hasFDerivWithinAt) (by simpa only [nhdsWithin_univ, sub_zero] using hRsmall)
  simpa only [R, quadraticError, add_zero, inner_zero_right, map_zero, sub_self,
    mul_zero, sub_zero, nhdsWithin_univ, Nat.reduceAdd] using ht

/-- Almost every point of a C¹ convex potential has a symmetric quadratic
expansion. The error estimate is pointwise, not uniform in the center. -/
theorem ae_quadratic_expansion_convex {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hC1 : ContDiff ℝ 1 u) (hdom : conjugateDomain u = univ) :
    ∀ᵐ x ∂volume, ∃ A : E m →L[ℝ] E m, A.toLinearMap.IsSymmetric ∧
      (∀ v, 0 ≤ inner ℝ (A v) v) ∧
      (fun h => quadraticError u x (gradient u x) A h) =o[𝓝 0] (fun h : E m => ‖h‖ ^ 2) := by
  filter_upwards [ae_differentiable_gradient_convex hu hC1 hdom] with x hx
  exact ⟨fderiv ℝ (gradient u) x, symmetric_gradient_derivative hC1.differentiable_one hx.hasFDerivAt,
    nonneg_gradient_derivative hu hC1.differentiable_one hx.hasFDerivAt,
    quadratic_expansion_of_hasFDerivAt_gradient hC1.differentiable_one hx.hasFDerivAt⟩

end Submission.Obl.Entropy__smooth_gaussian_transport
