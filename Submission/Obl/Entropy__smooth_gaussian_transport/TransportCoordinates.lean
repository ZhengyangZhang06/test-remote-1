import Submission.Obl.Entropy__smooth_gaussian_transport.NormalizedCoefficients

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def normalizedGradient (m : ℕ) (L : E m ≃L[ℝ] E m) :
    (E m →L[ℝ] ℝ) →L[ℝ] E m :=
  (InnerProductSpace.toDual ℝ (E m)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ContinuousLinearMap.compL ℝ (E m) (E m) ℝ).flip L.symm.toContinuousLinearMap)

theorem normalizedGradient_fderiv_comp {m : ℕ} {f : E m → ℝ}
    (hf : Differentiable ℝ f) (L : E m ≃L[ℝ] E m) (x : E m) :
    normalizedGradient m L (fderiv ℝ (fun z => f (L z)) x) = gradient f (L x) := by
  have he := ((hf (L x)).hasFDerivAt.comp x L.toContinuousLinearMap.hasFDerivAt).fderiv
  change fderiv ℝ (fun z => f (L z)) x = _ at he
  change (InnerProductSpace.toDual ℝ (E m)).symm
    ((fderiv ℝ (fun z => f (L z)) x).comp L.symm.toContinuousLinearMap) = _
  have he' : (fderiv ℝ (fun z => f (L z)) x).comp L.symm.toContinuousLinearMap = fderiv ℝ f (L x) := by
    rw [he]
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, L.apply_symm_apply]
  rw [he']
  rfl

theorem normalized_transport_increment {m : ℕ} {f U V : E m → ℝ}
    (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, (operatorMatrix (fderiv ℝ (gradient f) x)).PosDef)
    (heq : ∀ x, Real.log (fderiv ℝ (gradient f) x).det = U x + V (gradient f x))
    (L : E m ≃L[ℝ] E m) (z w : E m) :
    segmentMean (normalizedPrincipal L)
      (iteratedFDeriv ℝ 2 (fun y => f (L y)) z) (iteratedFDeriv ℝ 2 (fun y => f (L y)) w)
        (iteratedFDeriv ℝ 2 (fun y => f (L y)) w - iteratedFDeriv ℝ 2 (fun y => f (L y)) z) =
      V (normalizedGradient m L (fderiv ℝ (fun y => f (L y)) w)) -
        V (normalizedGradient m L (fderiv ℝ (fun y => f (L y)) z)) + (U (L w) - U (L z)) := by
  have hB (y : E m) :
      hessianOperator m (untransformHessian L (iteratedFDeriv ℝ 2 (fun z => f (L z)) y)) =
        fderiv ℝ (gradient f) (L y) := by
    rw [untransformHessian_iteratedFDeriv hf, hessianOperator_iteratedFDeriv hf]
  rw [normalizedPrincipal_increment L (by rw [hB]; exact hpos _)
    (by rw [hB]; exact hpos _), hB, hB, heq, heq,
    normalizedGradient_fderiv_comp (hf.differentiable (by norm_num)),
    normalizedGradient_fderiv_comp (hf.differentiable (by norm_num))]
  ring

end Submission.Obl.Entropy__smooth_gaussian_transport
