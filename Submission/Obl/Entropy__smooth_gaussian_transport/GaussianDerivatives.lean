import Submission.Obl.Entropy__smooth_gaussian_transport.GaussianKernel

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped Topology RealInnerProductSpace NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

private theorem gaussian_log_derivative {m : ℕ} (c : ℝ) (x : E m) :
    HasFDerivAt (fun y : E m => c - ‖y‖ ^ 2 / 2) (-(innerSL ℝ x)) x := by
  convert! (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.mul_const (1 / 2 : ℝ)).const_sub c) using 1
  · funext y
    ring
  · apply ContinuousLinearMap.ext
    intro v
    simp only [neg_apply, smul_apply, innerSL_apply_apply, smul_eq_mul]
    ring

/-- Polynomial growth of the logarithm's derivatives, in a form usable in the
quantitative chain rule. -/
private theorem gaussian_log_derivative_bound {m : ℕ} (c : ℝ) (x : E m)
    {i : ℕ} (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (fun y : E m => c - ‖y‖ ^ 2 / 2) x‖ ≤
      ((1 + ‖(innerSL ℝ : E m →L[ℝ] (E m →L[ℝ] ℝ))‖) * (1 + ‖x‖)) ^ i := by
  let N : ℝ := ‖(innerSL ℝ : E m →L[ℝ] (E m →L[ℝ] ℝ))‖
  let D : ℝ := (1 + N) * (1 + ‖x‖)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hD : 1 ≤ D := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith [norm_nonneg x])
  have hND : N ≤ D := by dsimp [D]; nlinarith [norm_nonneg x]
  have he : fderiv ℝ (fun y : E m => c - ‖y‖ ^ 2 / 2) = fun y => -(innerSL ℝ y) :=
    funext (fun y => (gaussian_log_derivative c y).fderiv)
  have he' : fderiv ℝ (fun y : E m => -(innerSL ℝ y)) =
      fun _ => -(innerSL ℝ : E m →L[ℝ] (E m →L[ℝ] ℝ)) := by
    funext y
    exact ((innerSL ℝ).hasFDerivAt.neg).fderiv
  cases i with
  | zero => omega
  | succ j =>
    rw [← norm_iteratedFDeriv_fderiv, he]
    cases j with
    | zero =>
      simp only [norm_iteratedFDeriv_zero, norm_neg, zero_add, pow_one]
      exact ((innerSL ℝ).le_opNorm x).trans (by dsimp only [N] at hN; nlinarith [norm_nonneg x, hN])
    | succ k =>
      rw [← norm_iteratedFDeriv_fderiv, he']
      cases k with
      | zero =>
        simp only [norm_iteratedFDeriv_zero, norm_neg]
        exact hND.trans (le_self_pow₀ hD (by omega))
      | succ k =>
        rw [iteratedFDeriv_succ_const]
        simp only [Pi.zero_apply, norm_zero]
        positivity

/-- Every derivative of the Gaussian is bounded by a polynomial times the
same Gaussian. This provides integrable majorants for the smoothing kernels. -/
theorem gaussianDensity_derivative_bound {m : ℕ} (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E m,
      ‖iteratedFDeriv ℝ n Submission.Lib.EntropyRemainder.gaussianDensity x‖ ≤
        C * (1 + ‖x‖) ^ n * Submission.Lib.EntropyRemainder.gaussianDensity x := by
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ ^ m
  have hc : 0 < c := by dsimp [c]; positivity
  let q : E m → ℝ := fun x => Real.log c - ‖x‖ ^ 2 / 2
  have hq : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) q :=
    contDiff_const.sub ((contDiff_id.norm_sq ℝ).div_const 2)
  have he : Real.exp ∘ q = Submission.Lib.EntropyRemainder.gaussianDensity (m := m) := by
    funext x
    simp only [Function.comp_def, q, Real.exp_sub, Real.exp_log hc]
    simp only [Submission.Lib.EntropyRemainder.gaussianDensity, c, div_eq_mul_inv, ← Real.exp_neg]
    congr 2
    ring
  let N : ℝ := 1 + ‖(innerSL ℝ : E m →L[ℝ] (E m →L[ℝ] ℝ))‖
  have hN : 0 < N := by dsimp [N]; positivity
  refine ⟨(n.factorial : ℝ) * N ^ n, by positivity, ?_⟩
  intro x
  have hbound := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) Real.contDiff_exp hq
    (n := n) (WithTop.coe_le_coe.mpr (le_top : (n : ENat) ≤ ⊤)) x (C := Real.exp (q x)) (D := N * (1 + ‖x‖))
    (fun i _ => by
      simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
        Real.iter_deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), le_refl])
    (fun i hi _ => gaussian_log_derivative_bound (Real.log c) x hi)
  rw [he] at hbound
  have hex : Real.exp (q x) = Submission.Lib.EntropyRemainder.gaussianDensity x :=
    congr_fun he x
  rw [hex, mul_pow] at hbound
  convert! hbound using 1 <;> ring

end Submission.Obl.Entropy__smooth_gaussian_transport
