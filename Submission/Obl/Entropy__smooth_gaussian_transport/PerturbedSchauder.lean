import Submission.Obl.Entropy__smooth_gaussian_transport.LaplacianSchauder
import Submission.Obl.Entropy__smooth_gaussian_transport.HolderInterpolation
import Submission.Obl.Entropy__smooth_gaussian_transport.HolderAbsorption
import Submission.Obl.Entropy__smooth_gaussian_transport.HessianCurrying

open Set

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem clm_product_holder {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T : X → Y →L[ℝ] Z} {f : X → Y} {ε L M C α : ℝ}
    (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hT : ∀ x, ‖T x‖ ≤ ε) (hf : ∀ x, ‖f x‖ ≤ M)
    (hTm : ∀ x y, ‖T x - T y‖ ≤ L * ‖x - y‖ ^ α)
    (hfm : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α) (x y : X) :
    ‖T x (f x) - T y (f y)‖ ≤ (ε * C + L * M) * ‖x - y‖ ^ α := by
  have he : T x (f x) - T y (f y) = T x (f x - f y) + (T x - T y) (f y) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [he]
  calc
    _ ≤ ‖T x (f x - f y)‖ + ‖(T x - T y) (f y)‖ := norm_add_le _ _
    _ ≤ ‖T x‖ * ‖f x - f y‖ + ‖T x - T y‖ * ‖f y‖ :=
      add_le_add ((T x).le_opNorm _) ((T x - T y).le_opNorm _)
    _ ≤ ε * (C * ‖x - y‖ ^ α) + (L * ‖x - y‖ ^ α) * M := by
      exact add_le_add
        (mul_le_mul (hT x) (hfm x y) (norm_nonneg _) hε)
        (mul_le_mul (hTm x y) (hf y) (norm_nonneg _) (mul_nonneg hL (Real.rpow_nonneg (norm_nonneg _) _)))
    _ = _ := by ring

/-- A small perturbation of the Laplacian admits an a priori Hölder bound
independent of the initial Hölder constant of its Hessian. -/
theorem perturbed_laplacian_schauder {m : ℕ} {α K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hK : 0 < K)
    (hS : ∀ (f : E m → ℝ) (M C : ℝ),
      ContDiff ℝ 2 f → HasCompactSupport f → 0 ≤ M → 0 ≤ C →
      (∀ x, ‖f x‖ ≤ M) →
      (∀ x y, |laplacian f x - laplacian f y| ≤ C * ‖x - y‖ ^ α) →
      ∀ x y, ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤
        K * (M + C) * ‖x - y‖ ^ α)
    {f g : E m → ℝ} {T : E m → (E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ}
    {M N G ε L t : ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hG : 0 ≤ G) (hε : 0 ≤ ε) (hL : 0 ≤ L) (ht : 0 < t)
    (hsmall : K * (ε + L * t ^ α) ≤ 1 / 2)
    (hb : ∀ x, ‖f x‖ ≤ M) (hdb : ∀ x, ‖fderiv ℝ f x‖ ≤ N)
    (hT : ∀ x, ‖T x‖ ≤ ε)
    (hTm : ∀ x y, ‖T x - T y‖ ≤ L * ‖x - y‖ ^ α)
    (hgm : ∀ x y, |g x - g y| ≤ G * ‖x - y‖ ^ α)
    (heq : ∀ x, laplacian f x = g x + T x (iteratedFDeriv ℝ 2 f x))
    (hex : ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ C * ‖x - y‖ ^ α) :
    ∀ x y, ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤
      (2 * K * (M + G + 2 * L * N / t)) * ‖x - y‖ ^ α := by
  let θ : ℝ := K * (ε + L * t ^ α)
  let B : ℝ := K * (M + G + 2 * L * N / t)
  have hθ : 0 ≤ θ := by dsimp only [θ]; positivity
  have hθ1 : θ < 1 := lt_of_le_of_lt hsmall (by norm_num)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hstep (C : ℝ) (hC : 0 ≤ C)
      (hc : ∀ x y, ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ C * ‖x - y‖ ^ α) :
      ∀ x y, ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤
        (θ * C + B) * ‖x - y‖ ^ α := by
    have hd : Differentiable ℝ (fderiv ℝ f) :=
      (hf.fderiv_right (by norm_num : (1 : WithTop ENat) + 1 ≤ 2)).differentiable_one
    have hD (x : E m) : ‖iteratedFDeriv ℝ 2 f x‖ ≤ 2 * N / t + C * t ^ α := by
      rw [← norm_second_fderiv]
      exact derivative_holder_interpolation hd hN hC hα.le ht hdb
        (fun x y => by rw [norm_second_fderiv_sub]; exact hc x y) x
    have hprod := clm_product_holder hε hL hT hD hTm hc
    have hmod (x y : E m) : |laplacian f x - laplacian f y| ≤
        (G + ε * C + L * (2 * N / t + C * t ^ α)) * ‖x - y‖ ^ α := by
      rw [heq x, heq y]
      have he : (g x + T x (iteratedFDeriv ℝ 2 f x)) - (g y + T y (iteratedFDeriv ℝ 2 f y)) =
          (g x - g y) + (T x (iteratedFDeriv ℝ 2 f x) - T y (iteratedFDeriv ℝ 2 f y)) := by ring
      rw [he]
      exact (abs_add_le _ _).trans ((add_le_add (hgm x y) (hprod x y)).trans_eq (by ring))
    have hh := hS f M (G + ε * C + L * (2 * N / t + C * t ^ α)) hf hfc hM
      (by positivity) hb hmod
    intro x y
    convert! hh x y using 1 <;> dsimp only [θ, B] <;> ring
  have hbound := holder_bound_absorption hα hθ hθ1 hB hex hstep
  have hconst : B / (1 - θ) ≤ 2 * B := by
    apply (div_le_iff₀ (sub_pos.mpr hθ1)).mpr
    have hh := mul_le_mul_of_nonneg_left hsmall hB
    change B * θ ≤ B * (1 / 2) at hh
    nlinarith
  intro x y
  exact (hbound x y).trans (mul_le_mul_of_nonneg_right
    (hconst.trans_eq (by dsimp only [B]; ring)) (Real.rpow_nonneg (norm_nonneg _) _))

end Submission.Obl.Entropy__smooth_gaussian_transport
