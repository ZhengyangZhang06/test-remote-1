import Mathlib

open Set

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem holder_of_lipschitz_and_bound {X Y : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {f : X → Y} {M L α : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hα : 0 < α) (hα1 : α ≤ 1)
    (hb : ∀ x, ‖f x‖ ≤ M) (hLip : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) :
    ∀ x y, ‖f x - f y‖ ≤ (L + 2 * M) * ‖x - y‖ ^ α := by
  intro x y
  have hp : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  by_cases hnear : ‖x - y‖ ≤ 1
  · have hd : ‖x - y‖ ≤ ‖x - y‖ ^ α := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg (x - y)) hnear hα.le hα1)
    exact (hLip x y).trans ((mul_le_mul_of_nonneg_left hd hL).trans (by nlinarith))
  · have hd : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow (le_of_not_ge hnear) hα.le
    have hh : ‖f x - f y‖ ≤ 2 * M := (norm_sub_le _ _).trans (by linarith [hb x, hb y])
    exact hh.trans (by nlinarith)

theorem compact_c1_bounded_holder {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ M C : ℝ, 0 < M ∧ 0 < C ∧ (∀ x, ‖f x‖ ≤ M) ∧
      ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α := by
  obtain ⟨M, hM, hb⟩ := (hfc.isCompact_range hf.continuous).isBounded.exists_pos_norm_le
  obtain ⟨L, hL, hD⟩ := ((hfc.fderiv ℝ).isCompact_range
    (hf.continuous_fderiv (by norm_num))).isBounded.exists_pos_norm_le
  have hLip : LipschitzWith ⟨L, hL.le⟩ f := lipschitzWith_of_nnnorm_fderiv_le
    hf.differentiable_one (fun x => by exact_mod_cast hD _ (mem_range_self x))
  refine ⟨M, L + 2 * M, hM, by positivity, fun x => hb _ (mem_range_self x), ?_⟩
  apply holder_of_lipschitz_and_bound hM.le hL.le hα hα1 (fun x => hb _ (mem_range_self x))
  intro x y
  have hh := hLip.dist_le_mul x y
  simp only [dist_eq_norm] at hh
  convert! hh using 1

/-- A Hölder bound near the support extends globally using a size bound for
the pairs separated by the prescribed positive distance. -/
theorem global_holder_of_near_support {X Y : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {f : X → Y} {S : Set X} {M C r α : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hr : 0 < r) (hα : 0 ≤ α)
    (hb : ∀ x, ‖f x‖ ≤ M) (hs : Function.support f ⊆ S)
    (hmod : ∀ x ∈ S, ∀ y, ‖x - y‖ < r → ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α) :
    ∀ x y, ‖f x - f y‖ ≤ (C + 2 * M / r ^ α) * ‖x - y‖ ^ α := by
  intro x y
  have hp : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  have hrp : 0 < r ^ α := Real.rpow_pos_of_pos hr _
  by_cases hnear : ‖x - y‖ < r
  · have hh : ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α := by
      by_cases hx : f x = 0
      · by_cases hy : f y = 0
        · simp only [hx, hy, sub_self, norm_zero]
          exact mul_nonneg hC hp
        · simpa only [norm_sub_rev] using hmod y (hs hy) x (by simpa only [norm_sub_rev] using hnear)
      · exact hmod x (hs hx) y hnear
    exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hp)
  · have hp' : r ^ α ≤ ‖x - y‖ ^ α := Real.rpow_le_rpow hr.le (le_of_not_gt hnear) hα
    calc
      _ ≤ 2 * M := (norm_sub_le _ _).trans (by linarith [hb x, hb y])
      _ = (2 * M / r ^ α) * r ^ α := (div_mul_cancel₀ _ hrp.ne').symm
      _ ≤ (2 * M / r ^ α) * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_left hp' (by positivity)
      _ ≤ _ := by nlinarith

end Submission.Obl.Entropy__smooth_gaussian_transport
