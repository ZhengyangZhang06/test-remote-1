import Submission.Obl.Entropy__smooth_gaussian_transport.CutoffConvergence
import Submission.Obl.Entropy__smooth_gaussian_transport.HessianOperators
import Submission.Obl.Entropy__smooth_gaussian_transport.FiniteSmoothExtension

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem hessian_directional_derivative {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℝ} (hf : ContDiff ℝ 3 f) (v x : X) :
    iteratedFDeriv ℝ 2 (fun y => fderiv ℝ f y v) x = fderiv ℝ (iteratedFDeriv ℝ 2 f) x v := by
  have hD : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have he : fderiv ℝ (fun y => fderiv ℝ f y v) = fun y => fderiv ℝ (fderiv ℝ f) y v :=
    funext (fderiv_directional_derivative (hf.of_le (by norm_num)) v)
  apply (hessianCurry X ℝ).injective
  rw [hessianCurry_iteratedFDeriv, he, fderiv_directional_derivative hD]
  let L : (X [×2]→L[ℝ] ℝ) →L[ℝ] (X →L[ℝ] X →L[ℝ] ℝ) :=
    (hessianCurry X ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 f) x :=
    hf.contDiffAt.differentiableAt_iteratedFDeriv (by norm_num)
  have hLd : HasFDerivAt L L (iteratedFDeriv ℝ 2 f x) := by
    exact ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := X [×2]→L[ℝ] ℝ) (F := X →L[ℝ] X →L[ℝ] ℝ) L
  have hcomp : HasFDerivAt (fun y => L (iteratedFDeriv ℝ 2 f y))
      (L.comp (fderiv ℝ (iteratedFDeriv ℝ 2 f) x)) x := by
    exact HasFDerivAt.comp (𝕜 := ℝ) (E := X) (F := X [×2]→L[ℝ] ℝ)
      (G := X →L[ℝ] X →L[ℝ] ℝ) (f := iteratedFDeriv ℝ 2 f) (g := L) x hLd hd.hasFDerivAt
  have hh := hcomp.fderiv
  have hfun : (fun y => hessianCurry X ℝ (iteratedFDeriv ℝ 2 f y)) = fderiv ℝ (fderiv ℝ f) :=
    funext (hessianCurry_iteratedFDeriv f)
  change fderiv ℝ (fun y => hessianCurry X ℝ (iteratedFDeriv ℝ 2 f y)) x = _ at hh
  rw [hfun] at hh
  convert! congrArg (fun T : X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ => T v) hh using 1

theorem hessian_directional_derivative_at {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {f : X → ℝ} {x : X} (hf : ContDiffAt ℝ 3 f x) (v : X) :
    iteratedFDeriv ℝ 2 (fun y => fderiv ℝ f y v) x = fderiv ℝ (iteratedFDeriv ℝ 2 f) x v := by
  obtain ⟨g, hg, hgc, he⟩ := exists_compact_contDiff_extension (n := 3) hf
  have hd := he.fderiv (𝕜 := ℝ)
  have hp : (fun y => fderiv ℝ g y v) =ᶠ[nhds x] (fun y => fderiv ℝ f y v) := hd.mono (fun y hy => congrArg (fun T => T v) hy)
  rw [← (hp.iteratedFDeriv ℝ 2).eq_of_nhds,
    ← (he.iteratedFDeriv ℝ 2).fderiv_eq, hessian_directional_derivative hg]

theorem differentiate_linear_equation {m : ℕ} {f g : E m → ℝ}
    {A : E m → (E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ} {x : E m}
    (hf : ContDiffAt ℝ 3 f x) (hg : DifferentiableAt ℝ g x) (hA : DifferentiableAt ℝ A x)
    (he : (fun y => A y (iteratedFDeriv ℝ 2 f y)) =ᶠ[nhds x] g) (v : E m) :
    A x (iteratedFDeriv ℝ 2 (fun y => fderiv ℝ f y v) x) =
      fderiv ℝ g x v - fderiv ℝ A x v (iteratedFDeriv ℝ 2 f x) := by
  have hH : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 f) x := hf.differentiableAt_iteratedFDeriv (by norm_num)
  have hh := (hA.hasFDerivAt.clm_apply hH.hasFDerivAt).fderiv
  rw [he.fderiv_eq] at hh
  have hv := congrArg (fun T : E m →L[ℝ] ℝ => T v) hh
  rw [hessian_directional_derivative_at hf]
  convert! (eq_sub_iff_add_eq.mpr hv.symm) using 1

end Submission.Obl.Entropy__smooth_gaussian_transport
