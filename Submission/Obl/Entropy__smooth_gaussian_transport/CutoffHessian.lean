import Submission.Obl.Entropy__smooth_gaussian_transport.HessianCurrying

open Set

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def productHessianCross {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] (p q : X →L[ℝ] ℝ) : X [×2]→L[ℝ] ℝ :=
  (hessianCurry X ℝ).symm (p.smulRight q + q.smulRight p)

theorem productHessianCross_apply {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] (p q : X →L[ℝ] ℝ) (v : Fin 2 → X) :
    productHessianCross p q v = p (v 0) * q (v 1) + q (v 0) * p (v 1) := by
  have hv : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
  rw [← hv, ← hessianCurry_apply]
  simp only [productHessianCross, LinearIsometryEquiv.apply_symm_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
  rfl

theorem productHessianCross_contDiff {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ENat} :
    ContDiff ℝ n (fun z : (X →L[ℝ] ℝ) × (X →L[ℝ] ℝ) => productHessianCross z.1 z.2) :=
  (hessianCurry X ℝ).symm.toContinuousLinearEquiv.contDiff.comp
    ((contDiff_fst.smulRight contDiff_snd).add (contDiff_snd.smulRight contDiff_fst))

theorem iteratedFDeriv_two_mul {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f g : X → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : X) :
    iteratedFDeriv ℝ 2 (fun x => f x * g x) x =
      f x • iteratedFDeriv ℝ 2 g x + g x • iteratedFDeriv ℝ 2 f x +
        productHessianCross (fderiv ℝ f x) (fderiv ℝ g x) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hfD : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ENat) + 1 ≤ 2)).differentiable_one
  have hgD : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (by norm_num : (1 : WithTop ENat) + 1 ≤ 2)).differentiable_one
  have he : fderiv ℝ (fun x => f x * g x) = fun x => f x • fderiv ℝ g x + g x • fderiv ℝ f x :=
    funext (fun x => fderiv_fun_mul (hfd x) (hgd x))
  have hh := (((hfd x).hasFDerivAt.smul (hgD x).hasFDerivAt).add
    ((hgd x).hasFDerivAt.smul (hfD x).hasFDerivAt)).fderiv
  change fderiv ℝ (fun z => f z • fderiv ℝ g z + g z • fderiv ℝ f z) x = _ at hh
  apply ContinuousMultilinearMap.ext
  intro v
  rw [iteratedFDeriv_two_apply, he]
  change fderiv ℝ (fun z => f z • fderiv ℝ g z + g z • fderiv ℝ f z) x (v 0) (v 1) = _
  rw [hh]
  simp only [ContinuousLinearMap.add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousMultilinearMap.add_apply, smul_eq_mul, iteratedFDeriv_two_apply, productHessianCross_apply]
  ring

end Submission.Obl.Entropy__smooth_gaussian_transport
