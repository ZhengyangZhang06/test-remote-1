import Submission.Obl.Entropy__smooth_gaussian_transport.AlmostEverywhereEquation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem symmetric_gradient_derivative {m : ℕ} {u : E m → ℝ}
    (hu : Differentiable ℝ u) {x : E m} {A : E m →L[ℝ] E m}
    (hA : HasFDerivAt (gradient u) A x) : A.toLinearMap.IsSymmetric := by
  let B : E m →L[ℝ] (E m →L[ℝ] ℝ) :=
    (InnerProductSpace.toDual ℝ (E m)).toContinuousLinearMap
  have hf' : HasFDerivAt (fderiv ℝ u) (B.comp A) x := by
    convert! B.hasFDerivAt.comp x hA using 1
    ext y z
    exact congrArg (fun p : E m →L[ℝ] ℝ => p z) (toDual_gradient (𝕜 := ℝ) (f := u) (x := y)).symm
  intro v w
  have hs := second_derivative_symmetric (fun y => (hu y).hasFDerivAt) hf' v w
  change inner ℝ (A v) w = inner ℝ (A w) v at hs
  change inner ℝ (A v) w = inner ℝ v (A w)
  exact hs.trans (real_inner_comm _ _)

theorem nonneg_gradient_derivative {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hd : Differentiable ℝ u) {x : E m}
    {A : E m →L[ℝ] E m} (hA : HasFDerivAt (gradient u) A x) (v : E m) :
    0 ≤ inner ℝ (A v) v := by
  let q : ℝ → ℝ := fun t => inner ℝ (gradient u (x + t • v)) v
  have hq : Monotone q := by
    intro s t hst
    rcases hst.eq_or_lt with rfl | hst
    · exact le_rfl
    have h := convex_gradient_monotone hu hd (x + t • v) (x + s • v)
    have hsub : (x + t • v) - (x + s • v) = (t - s) • v := by module
    rw [hsub, real_inner_smul_right, inner_sub_left] at h
    change inner ℝ (gradient u (x + s • v)) v ≤ inner ℝ (gradient u (x + t • v)) v
    nlinarith
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hcomp : HasDerivAt (fun t : ℝ => gradient u (x + t • v)) (A v) 0 := by
    have hA0 : HasFDerivAt (gradient u) A (x + (0 : ℝ) • v) := by simpa using hA
    exact hA0.comp_hasDerivAt 0 hline
  have hqd : HasDerivAt q (inner ℝ (A v) v) 0 := by
    simpa only [q, inner_zero_right, zero_add] using hcomp.inner ℝ (hasDerivAt_const (0 : ℝ) v)
  rw [← hqd.deriv]
  exact hq.deriv_nonneg

/-- Almost everywhere, the transport Hessian is symmetric, nonnegative and
invertible. These are pointwise conclusions and do not assert continuity of
the Hessian. -/
theorem brenier_ae_hessian_structure {m : ℕ} (hm : 1 ≤ m) {V φ : E m → ℝ}
    (hV : Continuous V) (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    ∀ᵐ x ∂volume, DifferentiableAt ℝ (gradient φ) x ∧
      (fderiv ℝ (gradient φ) x).toLinearMap.IsSymmetric ∧
      (∀ v, 0 ≤ inner ℝ (fderiv ℝ (gradient φ) x v) v) ∧
      (fderiv ℝ (gradient φ) x).det ≠ 0 := by
  have hd := (brenier_contDiff_one hm hV hφ hlaw).1.differentiable_one
  filter_upwards [brenier_ae_classical_density hm hV hφ hlaw] with x hx
  refine ⟨hx.1, symmetric_gradient_derivative hd hx.1.hasFDerivAt,
    nonneg_gradient_derivative hφ hd hx.1.hasFDerivAt, ?_⟩
  have hpos : 0 < |(fderiv ℝ (gradient φ) x).det| := by
    rw [hx.2]
    exact mul_pos (Submission.Lib.EntropyRemainder.gaussianDensity_pos x) (Real.exp_pos _)
  exact abs_pos.mp hpos

end Submission.Obl.Entropy__smooth_gaussian_transport
