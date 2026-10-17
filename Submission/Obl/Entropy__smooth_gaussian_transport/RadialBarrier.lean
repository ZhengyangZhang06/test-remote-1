import Submission.Obl.Entropy__smooth_gaussian_transport.RadialKernel
import Submission.Obl.Entropy__smooth_gaussian_transport.NormalizedDifferences

open MeasureTheory Set Filter InnerProductSpace
open scoped Topology RealInnerProductSpace NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem radialKernel_operator_annulus {m : ℕ} {p : ℕ} (hp : 1 ≤ p) (x : E m)
    {A : E m →L[ℝ] E m} {b : E m} {δ Λ M : ℝ}
    (hΛ0 : 0 ≤ Λ) (hM : 0 ≤ M) (hb : ‖b‖ ≤ M)
    (hδ : ∀ B : E m →L[ℝ] E m, (operatorMatrix B).PosSemidef →
      δ * ‖B‖ ≤ linearizedTrace A B)
    (hΛ : linearizedTrace A (ContinuousLinearMap.id ℝ (E m)) ≤ Λ)
    (hpδ : Λ + 4 * M + 1 ≤ ((p : ℝ) + 1) * δ)
    (hx1 : 1 ≤ ‖x‖) (hx4 : ‖x‖ ≤ 4) :
    4 / (17 : ℝ) ^ (p + 2) ≤
      linearizedTrace A (fderiv ℝ (gradient (radialKernel p)) x) -
        inner ℝ b (gradient (radialKernel p) x) := by
  let q : ℝ := 1 + ‖x‖ ^ 2
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq2 : q ≤ 2 * ‖x‖ ^ 2 := by dsimp [q]; nlinarith
  have hq17 : q ≤ 17 := by dsimp [q]; nlinarith [norm_nonneg x]
  have hΛq := mul_le_mul_of_nonneg_left hq2 hΛ0
  have hMq : M * ‖x‖ * q ≤ 8 * M * ‖x‖ ^ 2 := by
    calc
      _ ≤ (M * 4) * (2 * ‖x‖ ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hx4 hM) hq2 hq0.le (by positivity)
      _ = _ := by ring
  have hpq := mul_le_mul_of_nonneg_right hpδ (sq_nonneg ‖x‖)
  have hbracket : 2 ≤ 2 * ((p : ℝ) + 1) * δ * ‖x‖ ^ 2 - Λ * q - M * ‖x‖ * q := by
    nlinarith
  have hfactor :
      4 * (p : ℝ) * (p + 1) / q ^ (p + 2) * (δ * ‖x‖ ^ 2) -
        2 * p / q ^ (p + 1) * Λ - 2 * p / q ^ (p + 1) * (M * ‖x‖) =
      (2 * p / q ^ (p + 2)) *
        (2 * (p + 1) * δ * ‖x‖ ^ 2 - Λ * q - M * ‖x‖ * q) := by
    simp only [pow_succ]
    field_simp
    <;> ring
  have hden := one_div_le_one_div_of_le (pow_pos hq0 (p + 2))
    (pow_le_pow_left₀ hq0.le hq17 (p + 2))
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hnum := div_le_div_of_nonneg_right
    (show (4 : ℝ) ≤ 4 * p by linarith) (pow_nonneg hq0.le (p + 2))
  calc
    _ ≤ 4 / q ^ (p + 2) := by
      simpa only [← mul_div_assoc, mul_one] using mul_le_mul_of_nonneg_left hden (by norm_num : (0 : ℝ) ≤ 4)
    _ ≤ (2 * (p : ℝ) / q ^ (p + 2)) * 2 := by convert! hnum using 1 <;> ring
    _ ≤ (2 * (p : ℝ) / q ^ (p + 2)) *
        (2 * (p + 1) * δ * ‖x‖ ^ 2 - Λ * q - M * ‖x‖ * q) :=
      mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ = _ := hfactor.symm
    _ ≤ _ := radialKernel_operator_lower p x hM hb hδ hΛ

theorem radialKernel_operator_ball {m : ℕ} (p : ℕ) (x : E m)
    {A : E m →L[ℝ] E m} {b : E m} {δ Λ M : ℝ}
    (hδ0 : 0 ≤ δ) (hΛ0 : 0 ≤ Λ) (hM : 0 ≤ M) (hb : ‖b‖ ≤ M)
    (hδ : ∀ B : E m →L[ℝ] E m, (operatorMatrix B).PosSemidef →
      δ * ‖B‖ ≤ linearizedTrace A B)
    (hΛ : linearizedTrace A (ContinuousLinearMap.id ℝ (E m)) ≤ Λ)
    (hx4 : ‖x‖ ≤ 4) :
    -(2 * (p : ℝ) * Λ + 8 * p * M) ≤
      linearizedTrace A (fderiv ℝ (gradient (radialKernel p)) x) -
        inner ℝ b (gradient (radialKernel p) x) := by
  have hq : 1 ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
  have hc0 : 0 ≤ 2 * (p : ℝ) / (1 + ‖x‖ ^ 2) ^ (p + 1) := by positivity
  have hc : 2 * (p : ℝ) / (1 + ‖x‖ ^ 2) ^ (p + 1) ≤ 2 * p :=
    div_le_self (by positivity) (one_le_pow₀ hq)
  have h₁ := mul_le_mul_of_nonneg_right hc hΛ0
  have h₂ := mul_le_mul hc (mul_le_mul_of_nonneg_left hx4 hM)
    (mul_nonneg hM (norm_nonneg x)) (by positivity : 0 ≤ 2 * (p : ℝ))
  have h₃ : 0 ≤ 4 * (p : ℝ) * (p + 1) / (1 + ‖x‖ ^ 2) ^ (p + 2) *
      (δ * ‖x‖ ^ 2) := by positivity
  have hlow := radialKernel_operator_lower p x hM hb hδ hΛ
  linarith

noncomputable def radialBarrier {m : ℕ} (p : ℕ) (B : ℝ) (x : E m) : ℝ :=
  B * ((17 ^ p : ℝ)⁻¹ - radialKernel p x)

theorem radialBarrier_contDiff {m : ℕ} (p : ℕ) (B : ℝ) {n : WithTop ENat} :
    ContDiff ℝ n (radialBarrier (m := m) p B) :=
  contDiff_const.mul (contDiff_const.sub (radialKernel_contDiff p))

theorem radialBarrier_gradient {m : ℕ} (p : ℕ) (B : ℝ) (x : E m) :
    gradient (radialBarrier p B) x = (-B) • gradient (radialKernel p) x := by
  have hd : Differentiable ℝ (fun y : E m => (17 ^ p : ℝ)⁻¹ - radialKernel p y) :=
    (differentiable_const _).sub (radialKernel_contDiff p (n := 1)).differentiable_one
  calc
    _ = B • gradient (fun y : E m => (17 ^ p : ℝ)⁻¹ - radialKernel p y) x :=
      gradient_const_mul_of_differentiable hd B x
    _ = B • (-gradient (radialKernel p) x) := congrArg (B • ·)
      (gradient_const_sub_of_differentiable
        (radialKernel_contDiff p (n := 1)).differentiable_one _ x)
    _ = _ := by simp only [smul_neg, neg_smul]

theorem radialBarrier_gradient_lipschitz {m : ℕ} (p : ℕ) (B : ℝ) :
    ∃ L : NNReal, LipschitzWith L (gradient (radialBarrier (m := m) p B)) := by
  obtain ⟨L, hL⟩ := radialKernel_gradient_lipschitz (m := m) p
  refine ⟨‖-B‖₊ * L, ?_⟩
  rw [funext (radialBarrier_gradient p B)]
  exact (lipschitzWith_smul (-B)).comp hL

theorem radialBarrier_operator {m : ℕ} (p : ℕ) (B : ℝ) (x : E m)
    (A : E m →L[ℝ] E m) (b : E m) :
    linearizedTrace A (fderiv ℝ (gradient (radialBarrier p B)) x) -
        inner ℝ b (gradient (radialBarrier p B) x) =
      -B * (linearizedTrace A (fderiv ℝ (gradient (radialKernel p)) x) -
        inner ℝ b (gradient (radialKernel p) x)) := by
  have hd : HasFDerivAt (gradient (radialBarrier p B))
      ((-B) • fderiv ℝ (gradient (radialKernel p)) x) x := by
    rw [funext (radialBarrier_gradient p B)]
    exact (radialKernel_gradient_hasFDerivAt p x).differentiableAt.hasFDerivAt.const_smul (-B)
  rw [hd.fderiv, linearizedTrace_smul, radialBarrier_gradient, real_inner_smul_right]
  ring

/-- A barrier which vanishes at radius four, is below minus two at radius
three, and has a strictly negative elliptic operator outside the unit ball.
The constants are uniform over all coefficients with the stated bounds. -/
theorem exists_elliptic_radial_barrier {m : ℕ} {δ Λ M : ℝ}
    (hδ : 0 < δ) (hΛ : 0 ≤ Λ) (hM : 0 ≤ M) :
    ∃ (ψ : E m → ℝ) (T N : ℝ), 1 < T ∧ 0 < N ∧
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) ψ ∧
      (∃ L : NNReal, LipschitzWith L (gradient ψ)) ∧
      (∀ x, -T ≤ ψ x) ∧ (∀ x, ‖x‖ = 4 → ψ x = 0) ∧
      (∀ x, ‖x‖ ≤ 3 → ψ x ≤ -2) ∧
      ∀ (x : E m) (A : E m →L[ℝ] E m) (b : E m), ‖x‖ ≤ 4 → ‖b‖ ≤ M →
        (∀ B : E m →L[ℝ] E m, (operatorMatrix B).PosSemidef →
          δ * ‖B‖ ≤ linearizedTrace A B) →
        linearizedTrace A (ContinuousLinearMap.id ℝ (E m)) ≤ Λ →
        linearizedTrace A (fderiv ℝ (gradient ψ) x) - inner ℝ b (gradient ψ x) ≤ N ∧
          (1 ≤ ‖x‖ → linearizedTrace A (fderiv ℝ (gradient ψ) x) -
            inner ℝ b (gradient ψ x) ≤ -(2 + M / 8)) := by
  obtain ⟨p, hp⟩ := exists_nat_gt (max 1 ((Λ + 4 * M + 1) / δ))
  have hp1 : 1 ≤ p := by exact_mod_cast (le_max_left _ _ |>.trans hp.le)
  have hpδ : Λ + 4 * M + 1 ≤ ((p : ℝ) + 1) * δ := by
    have hh := (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hp)
    nlinarith
  let d : ℝ := (10 ^ p : ℝ)⁻¹ - (17 ^ p : ℝ)⁻¹
  let ε : ℝ := 4 / (17 : ℝ) ^ (p + 2)
  have hd : 0 < d := by
    have hh := one_div_lt_one_div_of_lt (by positivity : (0 : ℝ) < 10 ^ p)
      (pow_lt_pow_left₀ (by norm_num : (10 : ℝ) < 17) (by norm_num) (by omega : p ≠ 0))
    dsimp [d]
    simpa only [one_div, sub_pos] using hh
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨B, hB⟩ := exists_gt (max 1 (max (2 / d) ((2 + M / 8) / ε)))
  have hB1 : 1 < B := (le_max_left _ _).trans_lt hB
  have hB0 : 0 < B := zero_lt_one.trans hB1
  have hBd : 2 ≤ B * d := by
    have hh := (le_max_left (2 / d) ((2 + M / 8) / ε)).trans (le_max_right 1 _)
    exact ((div_lt_iff₀ hd).mp (hh.trans_lt hB)).le
  have hBε : 2 + M / 8 ≤ B * ε := by
    have hh := (le_max_right (2 / d) ((2 + M / 8) / ε)).trans (le_max_right 1 _)
    exact ((div_lt_iff₀ hε).mp (hh.trans_lt hB)).le
  refine ⟨radialBarrier p B, B + 1, 1 + B * (2 * p * Λ + 8 * p * M),
    by linarith, by positivity, radialBarrier_contDiff p B,
    radialBarrier_gradient_lipschitz p B, ?_, ?_, ?_, ?_⟩
  · intro x
    have hk := radialKernel_le_one p x
    have hc : 0 ≤ (17 ^ p : ℝ)⁻¹ := by positivity
    dsimp [radialBarrier]
    nlinarith
  · intro x hx
    simp only [radialBarrier, radialKernel, hx]
    norm_num
  · intro x hx
    have hq : 1 + ‖x‖ ^ 2 ≤ (10 : ℝ) := by nlinarith [norm_nonneg x]
    have hk : (10 ^ p : ℝ)⁻¹ ≤ radialKernel p x := by
      simpa only [one_div, radialKernel] using
        one_div_le_one_div_of_le (pow_pos (by positivity : 0 < 1 + ‖x‖ ^ 2) p)
          (pow_le_pow_left₀ (by positivity) hq p)
    dsimp [radialBarrier]
    dsimp [d] at hBd
    nlinarith
  · intro x A b hx hb hc hA
    rw [radialBarrier_operator]
    have hball := radialKernel_operator_ball p x hδ.le hΛ hM hb hc hA hx
    constructor
    · nlinarith
    · intro hx1
      have hann := radialKernel_operator_annulus hp1 x hΛ hM hb hc hA hpδ hx1 hx
      change ε ≤ _ at hann
      nlinarith

end Submission.Obl.Entropy__smooth_gaussian_transport
