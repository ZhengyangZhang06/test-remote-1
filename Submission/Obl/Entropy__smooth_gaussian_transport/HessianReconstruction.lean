import Submission.Obl.Entropy__smooth_gaussian_transport.HessianOperators

open scoped RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def hessianOfOperator (m : ℕ) :
    (E m →L[ℝ] E m) →L[ℝ] (E m [×2]→L[ℝ] ℝ) :=
  (hessianCurry (E m) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.compL ℝ (E m) (E m) (E m →L[ℝ] ℝ)
      (InnerProductSpace.toDual ℝ (E m)).toContinuousLinearEquiv.toContinuousLinearMap)

theorem hessianOfOperator_apply {m : ℕ} (A : E m →L[ℝ] E m) (v : Fin 2 → E m) :
    hessianOfOperator m A v = inner ℝ (A (v 0)) (v 1) := by
  have he : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
  rw [← he, ← hessianCurry_apply]
  change (hessianCurry (E m) ℝ) ((hessianCurry (E m) ℝ).symm _) (v 0) (v 1) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem hessianOfOperator_hessianOperator {m : ℕ} (B : E m [×2]→L[ℝ] ℝ) :
    hessianOfOperator m (hessianOperator m B) = B := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [hessianOfOperator_apply, hessianOperator_inner]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem hessianOfOperator_fderiv_gradient {m : ℕ} {f : E m → ℝ}
    (hf : ContDiff ℝ 2 f) (x : E m) :
    hessianOfOperator m (fderiv ℝ (gradient f) x) = iteratedFDeriv ℝ 2 f x := by
  rw [← hessianOperator_iteratedFDeriv hf, hessianOfOperator_hessianOperator]

end Submission.Obl.Entropy__smooth_gaussian_transport
