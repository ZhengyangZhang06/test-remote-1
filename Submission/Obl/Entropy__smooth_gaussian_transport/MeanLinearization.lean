import Submission.Obl.Entropy__smooth_gaussian_transport.LogDetDerivative
import Submission.Obl.Entropy__smooth_gaussian_transport.ClassicalTransport

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem positive_hessian_segment {m : ℕ} {A B : E m →L[ℝ] E m}
    (hA : (operatorMatrix A).PosDef) (hB : (operatorMatrix B).PosDef)
    {t : ℝ} (ht : t ∈ Icc 0 1) : (operatorMatrix (A + t • (B - A))).PosDef := by
  have he : A + t • (B - A) = (1 - t) • A + t • B := by module
  rw [he]
  have hm : operatorMatrix ((1 - t) • A + t • B) =
      (1 - t) • operatorMatrix A + t • operatorMatrix B := by
    simp only [operatorMatrix, ContinuousLinearMap.toLinearMap_add,
      ContinuousLinearMap.toLinearMap_smul, map_add, map_smul]
  rw [hm]
  rcases ht.2.eq_or_lt with he | he
  · subst t
    simpa using hB
  · exact (hA.smul (sub_pos.mpr he)).add_posSemidef (hB.posSemidef.smul ht.1)

/-- The exact difference of two log determinants is the average of their
linearizations along the positive segment joining them. -/
theorem log_det_sub_eq_integral {m : ℕ} {A B : E m →L[ℝ] E m}
    (hA : (operatorMatrix A).PosDef) (hB : (operatorMatrix B).PosDef) :
    Real.log B.det - Real.log A.det =
      ∫ t in (0 : ℝ)..1, linearizedTrace (A + t • (B - A)) (B - A) := by
  have hAs : A.toLinearMap.IsSymmetric :=
    ((LinearMap.posSemidef_toMatrix_iff (EuclideanSpace.basisFun (Fin m) ℝ)).mp hA.posSemidef).1
  have hBs : B.toLinearMap.IsSymmetric :=
    ((LinearMap.posSemidef_toMatrix_iff (EuclideanSpace.basisFun (Fin m) ℝ)).mp hB.posSemidef).1
  have hcont : ContinuousOn (fun t : ℝ => linearizedTrace (A + t • (B - A)) (B - A)) (Icc 0 1) := by
    intro t ht
    have hn : (A + t • (B - A)).det ≠ 0 := by
      simpa only [operatorMatrix_det] using (positive_hessian_segment hA hB ht).det_pos.ne'
    exact ((linearizedTrace_continuousAt (B := B - A) hn).comp (f := fun s : ℝ => (A + s • (B - A), B - A))
      (by fun_prop : ContinuousAt (fun s : ℝ => (A + s • (B - A), B - A)) t)).continuousWithinAt
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t ht =>
      hasDerivAt_log_det_line (positive_hessian_segment hA hB (by simpa using ht)) (hBs.sub hAs))
    (hcont.intervalIntegrable_of_Icc (by norm_num))
  have he : A + (B - A) = B := by abel
  have he0 : A + (0 : ℝ) • (B - A) = A := by ext v; simp
  simpa only [one_smul, he0, he] using hh.symm

/-- The same exact mean-value identity for the target potential. -/
theorem potential_sub_eq_integral_gradient {m : ℕ} {V : E m → ℝ}
    (hV : ContDiff ℝ 1 V) (x y : E m) :
    V y - V x = ∫ t in (0 : ℝ)..1, inner ℝ (gradient V (x + t • (y - x))) (y - x) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => V (x + s • (y - x)))
      (inner ℝ (gradient V (x + t • (y - x))) (y - x)) t := by
    intro t
    have hh := (hV.differentiable_one (x + t • (y - x))).hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const (y - x)).const_add x)
    convert! hh using 1
    simpa only [one_smul, InnerProductSpace.toDual_apply_apply] using
      congrArg (fun p : E m →L[ℝ] ℝ => p (y - x))
        (toDual_gradient (𝕜 := ℝ) (f := V) (x := x + t • (y - x)))
  have hc : Continuous (fun t : ℝ => inner ℝ (gradient V (x + t • (y - x))) (y - x)) :=
    ((continuous_gradient_of_contDiff_one hV).comp
      (continuous_const.add (continuous_id.smul continuous_const))).inner continuous_const
  have he : x + (y - x) = y := by abel
  simpa only [one_smul, zero_smul, add_zero, he] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hc.intervalIntegrable 0 1)).symm

theorem log_gaussianDensity_sub {m : ℕ} (x h : E m) :
    Real.log (Submission.Lib.EntropyRemainder.gaussianDensity (x + h)) -
      Real.log (Submission.Lib.EntropyRemainder.gaussianDensity x) =
        -inner ℝ x h - ‖h‖ ^ 2 / 2 := by
  have hc : ((Real.sqrt (2 * Real.pi))⁻¹ ^ m : ℝ) ≠ 0 := by positivity
  simp only [Submission.Lib.EntropyRemainder.gaussianDensity,
    Real.log_mul hc (Real.exp_ne_zero _), Real.log_exp]
  nlinarith [norm_add_sq_real x h]

/-- An exact linear equation for finite increments of the classical transport.
The coefficients are averages along positive Hessian and gradient segments. -/
theorem brenier_increment_equation {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) (x h : E m) :
    (∫ t in (0 : ℝ)..1, linearizedTrace
      (fderiv ℝ (gradient φ) x + t • (fderiv ℝ (gradient φ) (x + h) - fderiv ℝ (gradient φ) x))
      (fderiv ℝ (gradient φ) (x + h) - fderiv ℝ (gradient φ) x)) -
    (∫ t in (0 : ℝ)..1, inner ℝ
      (gradient V (gradient φ x + t • (gradient φ (x + h) - gradient φ x)))
      (gradient φ (x + h) - gradient φ x)) = -inner ℝ x h - ‖h‖ ^ 2 / 2 := by
  rw [← log_det_sub_eq_integral (brenier_positive_hessian hm hV ha hH hφ hlaw x).1
      (brenier_positive_hessian hm hV ha hH hφ hlaw (x + h)).1,
    ← potential_sub_eq_integral_gradient (hV.of_le (by norm_num)),
    brenier_log_det_equation hm hV ha hH hφ hlaw (x + h),
    brenier_log_det_equation hm hV ha hH hφ hlaw x]
  have hh := log_gaussianDensity_sub x h
  linarith

end Submission.Obl.Entropy__smooth_gaussian_transport
