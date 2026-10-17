import Submission.Obl.Entropy__smooth_gaussian_transport.LinearizedEllipticity

open MeasureTheory Set Filter InnerProductSpace
open scoped Topology RealInnerProductSpace NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem hasDerivAt_inverse_nat_pow (n : ℕ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => (s ^ n)⁻¹) (-(n : ℝ) / t ^ (n + 1)) t := by
  cases n with
  | zero => simpa using (hasDerivAt_const t (1 : ℝ))
  | succ n =>
    convert! ((hasDerivAt_pow (n + 1) t).inv (pow_ne_zero _ ht)) using 1
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    simp only [pow_succ]
    field_simp

/-- A smooth radial kernel used to localize contact points in the ABP estimate. -/
noncomputable def radialKernel {m : ℕ} (p : ℕ) (x : E m) : ℝ :=
  ((1 + ‖x‖ ^ 2) ^ p)⁻¹

theorem radialKernel_contDiff {m : ℕ} (p : ℕ) {n : WithTop ENat} :
    ContDiff ℝ n (radialKernel (m := m) p) := by
  exact (((contDiff_const.add (contDiff_id.norm_sq ℝ)).pow p).inv
    (fun x => pow_ne_zero _ (by positivity)))

theorem radialKernel_hasFDerivAt {m : ℕ} (p : ℕ) (x : E m) :
    HasFDerivAt (radialKernel p)
      ((-2 * (p : ℝ) / (1 + ‖x‖ ^ 2) ^ (p + 1)) • innerSL ℝ x) x := by
  have hq : HasFDerivAt (fun y : E m => 1 + ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add 1
  convert! (hasDerivAt_inverse_nat_pow p (by positivity : 1 + ‖x‖ ^ 2 ≠ 0)).comp_hasFDerivAt x hq using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply_apply]
  ring

theorem radialKernel_gradient {m : ℕ} (p : ℕ) (x : E m) :
    gradient (radialKernel p) x = (-2 * (p : ℝ) / (1 + ‖x‖ ^ 2) ^ (p + 1)) • x := by
  simp only [gradient, (radialKernel_hasFDerivAt p x).fderiv, map_smul]
  congr 1
  exact (toDual ℝ (E m)).symm_apply_apply x

theorem radialKernel_gradient_hasFDerivAt {m : ℕ} (p : ℕ) (x : E m) :
    HasFDerivAt (gradient (radialKernel p))
      ((4 * (p : ℝ) * (p + 1) / (1 + ‖x‖ ^ 2) ^ (p + 2)) • rankOne ℝ x x -
       (2 * (p : ℝ) / (1 + ‖x‖ ^ 2) ^ (p + 1)) • ContinuousLinearMap.id ℝ (E m)) x := by
  have hd := ((radialKernel_hasFDerivAt (p + 1) x).const_mul (-2 * (p : ℝ))).smul
    (hasFDerivAt_id x)
  have he : gradient (radialKernel p) = fun y : E m =>
      (-2 * (p : ℝ) * radialKernel (p + 1) y) • y := by
    funext y
    rw [radialKernel_gradient]
    simp only [radialKernel, div_eq_mul_inv]
  rw [he]
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, rankOne_apply,
    radialKernel, smul_smul, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, id_eq]
  module

theorem operatorMatrix_rankOne_posSemidef {m : ℕ} (x : E m) :
    (operatorMatrix (rankOne ℝ x x)).PosSemidef := by
  apply operatorMatrix_posSemidef (isSymmetric_rankOne_self x)
  intro v
  simp only [rankOne_apply, real_inner_smul_left]
  exact mul_self_nonneg _

theorem radialKernel_pos {m : ℕ} (p : ℕ) (x : E m) : 0 < radialKernel p x := by
  unfold radialKernel
  positivity

theorem radialKernel_le_one {m : ℕ} (p : ℕ) (x : E m) : radialKernel p x ≤ 1 := by
  apply inv_le_one_of_one_le₀
  exact one_le_pow₀ (by nlinarith [sq_nonneg ‖x‖])

theorem radialKernel_hessian_norm_le {m : ℕ} (p : ℕ) (x : E m) :
    ‖fderiv ℝ (gradient (radialKernel p)) x‖ ≤ 4 * (p : ℝ) * (p + 1) + 2 * p := by
  let q : ℝ := 1 + ‖x‖ ^ 2
  have hq : 1 ≤ q := by dsimp [q]; nlinarith [sq_nonneg ‖x‖]
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hr : ‖x‖ ^ 2 ≤ q ^ (p + 2) :=
    (show ‖x‖ ^ 2 ≤ q by dsimp [q]; linarith).trans (le_self_pow₀ hq (by omega))
  have h₁ : ‖x‖ ^ 2 / q ^ (p + 2) ≤ 1 := (div_le_one (pow_pos hq0 _)).mpr hr
  have h₂ : 1 / q ^ (p + 1) ≤ 1 :=
    (div_le_one (pow_pos hq0 _)).mpr (one_le_pow₀ hq)
  rw [(radialKernel_gradient_hasFDerivAt p x).fderiv]
  calc
    _ ≤ ‖(4 * (p : ℝ) * (p + 1) / q ^ (p + 2)) • rankOne ℝ x x‖ +
        ‖(2 * (p : ℝ) / q ^ (p + 1)) • ContinuousLinearMap.id ℝ (E m)‖ := norm_sub_le _ _
    _ = (4 * (p : ℝ) * (p + 1) / q ^ (p + 2)) * ‖x‖ ^ 2 +
        (2 * (p : ℝ) / q ^ (p + 1)) * ‖ContinuousLinearMap.id ℝ (E m)‖ := by
      simp only [norm_smul, Real.norm_eq_abs, norm_rankOne]
      rw [abs_of_nonneg (by positivity : 0 ≤ 4 * (p : ℝ) * (p + 1) / q ^ (p + 2)),
        abs_of_nonneg (by positivity : 0 ≤ 2 * (p : ℝ) / q ^ (p + 1))]
      ring
    _ ≤ (4 * (p : ℝ) * (p + 1)) * (‖x‖ ^ 2 / q ^ (p + 2)) +
        (2 * (p : ℝ)) * (1 / q ^ (p + 1)) := by
      have hh := mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E m))
        (by positivity : 0 ≤ 2 * (p : ℝ) / q ^ (p + 1))
      convert! add_le_add_left hh ((4 * (p : ℝ) * (p + 1) / q ^ (p + 2)) * ‖x‖ ^ 2) using 1 <;> ring
    _ ≤ 4 * (p : ℝ) * (p + 1) + 2 * p := by
      nlinarith [mul_le_mul_of_nonneg_left h₁ (by positivity : 0 ≤ 4 * (p : ℝ) * (p + 1)),
        mul_le_mul_of_nonneg_left h₂ (by positivity : 0 ≤ 2 * (p : ℝ))]

theorem radialKernel_gradient_lipschitz {m : ℕ} (p : ℕ) :
    ∃ L : NNReal, LipschitzWith L (gradient (radialKernel (m := m) p)) := by
  refine ⟨⟨4 * (p : ℝ) * (p + 1) + 2 * p, by positivity⟩, ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le
    (fun x => (radialKernel_gradient_hasFDerivAt p x).differentiableAt)
  intro x
  exact radialKernel_hessian_norm_le p x

theorem radialKernel_operator_lower {m : ℕ} (p : ℕ) (x : E m)
    {A : E m →L[ℝ] E m} {b : E m} {δ Λ M : ℝ}
    (hM : 0 ≤ M) (hb : ‖b‖ ≤ M)
    (hδ : ∀ B : E m →L[ℝ] E m, (operatorMatrix B).PosSemidef →
      δ * ‖B‖ ≤ linearizedTrace A B)
    (hΛ : linearizedTrace A (ContinuousLinearMap.id ℝ (E m)) ≤ Λ) :
    4 * (p : ℝ) * (p + 1) / (1 + ‖x‖ ^ 2) ^ (p + 2) * (δ * ‖x‖ ^ 2) -
        2 * p / (1 + ‖x‖ ^ 2) ^ (p + 1) * Λ -
        2 * p / (1 + ‖x‖ ^ 2) ^ (p + 1) * (M * ‖x‖) ≤
      linearizedTrace A (fderiv ℝ (gradient (radialKernel p)) x) -
        inner ℝ b (gradient (radialKernel p) x) := by
  have hR := hδ _ (operatorMatrix_rankOne_posSemidef x)
  simp only [norm_rankOne, ← pow_two] at hR
  have hi : -(M * ‖x‖) ≤ inner ℝ b x := by
    have hh := (abs_le.mp (abs_real_inner_le_norm b x)).1
    have hm := mul_le_mul_of_nonneg_right hb (norm_nonneg x)
    linarith
  have hc : 0 ≤ 2 * (p : ℝ) / (1 + ‖x‖ ^ 2) ^ (p + 1) := by positivity
  have hd : 0 ≤ 4 * (p : ℝ) * (p + 1) / (1 + ‖x‖ ^ 2) ^ (p + 2) := by positivity
  rw [(radialKernel_gradient_hasFDerivAt p x).fderiv,
    linearizedTrace_sub, linearizedTrace_smul, linearizedTrace_smul,
    radialKernel_gradient, real_inner_smul_right]
  have h₁ := mul_le_mul_of_nonneg_left hR hd
  have h₂ := mul_le_mul_of_nonneg_left hΛ hc
  have h₃ := mul_le_mul_of_nonneg_left hi hc
  have hn : -2 * (p : ℝ) / (1 + ‖x‖ ^ 2) ^ (p + 1) =
      -(2 * (p : ℝ) / (1 + ‖x‖ ^ 2) ^ (p + 1)) := by ring
  rw [hn]
  linarith

end Submission.Obl.Entropy__smooth_gaussian_transport
