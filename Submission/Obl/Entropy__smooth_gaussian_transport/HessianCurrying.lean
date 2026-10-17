import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def hessianCurry (X Y : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] :
    (X [×2]→L[ℝ] Y) ≃ₗᵢ[ℝ] X →L[ℝ] X →L[ℝ] Y :=
  (continuousMultilinearCurryRightEquiv' ℝ 1 X Y).trans
    (continuousMultilinearCurryFin1 ℝ X (X →L[ℝ] Y))

theorem hessianCurry_apply {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : X [×2]→L[ℝ] Y) (v w : X) :
    hessianCurry X Y A v w = A ![v, w] := by
  simp only [hessianCurry, LinearIsometryEquiv.trans_apply,
    continuousMultilinearCurryFin1_apply, continuousMultilinearCurryRightEquiv_apply']
  congr 1
  ext i
  fin_cases i <;> rfl

theorem hessianCurry_iteratedFDeriv {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X → Y) (x : X) :
    hessianCurry X Y (iteratedFDeriv ℝ 2 f x) = fderiv ℝ (fderiv ℝ f) x := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rw [hessianCurry_apply, iteratedFDeriv_two_apply]
  rfl

theorem norm_second_fderiv_sub {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X → Y) (x y : X) :
    ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ =
      ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ := by
  have hh := (hessianCurry X Y).norm_map
    (iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y)
  have he := (hessianCurry X Y).map_sub
    (iteratedFDeriv ℝ 2 f x) (iteratedFDeriv ℝ 2 f y)
  rw [he, hessianCurry_iteratedFDeriv, hessianCurry_iteratedFDeriv] at hh
  exact hh

theorem norm_second_fderiv {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X → Y) (x : X) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [← hessianCurry_iteratedFDeriv f x, LinearIsometryEquiv.norm_map]

end Submission.Obl.Entropy__smooth_gaussian_transport
