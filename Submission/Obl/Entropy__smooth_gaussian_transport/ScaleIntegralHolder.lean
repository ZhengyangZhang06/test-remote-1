import Mathlib

open MeasureTheory Set Filter
open scoped Topology

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Integrating scale-wise size and Lipschitz estimates yields a Hölder estimate.
The split is at the distance between the two spatial points. -/
theorem scale_integral_holder {X Y : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {F : ℝ → X → Y} {α A B : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hi : ∀ x, IntegrableOn (fun r => F r x) (Ioi 0) volume)
    (hsize : ∀ r, 0 < r → ∀ x, ‖F r x‖ ≤ A * r ^ (α - 1))
    (hlip : ∀ r, 0 < r → ∀ x y, ‖F r x - F r y‖ ≤ B * r ^ (α - 2) * ‖x - y‖)
    (x y : X) :
    ‖(∫ r in Ioi 0, F r x) - ∫ r in Ioi 0, F r y‖ ≤
      (2 * A / α + B / (1 - α)) * ‖x - y‖ ^ α := by
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero, le_refl]
  let d : ℝ := ‖x - y‖
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hni : IntegrableOn (fun r : ℝ => r ^ (α - 1)) (Ioc 0 d) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hd.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  have hfi : IntegrableOn (fun r : ℝ => r ^ (α - 2)) (Ioi d) volume :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hd
  have hnint : (∫ r in Ioc 0 d, r ^ (α - 1)) = d ^ α / α := by
    rw [← intervalIntegral.integral_of_le hd.le, integral_rpow (Or.inl (by linarith : -1 < α - 1))]
    simp only [sub_add_cancel, Real.zero_rpow hα.ne', sub_zero]
  have hfint : (∫ r in Ioi d, r ^ (α - 2)) = d ^ (α - 1) / (1 - α) := by
    rw [integral_Ioi_rpow_of_lt (by linarith : α - 2 < -1) hd]
    have he : α - 2 + 1 = α - 1 := by ring
    rw [he]
    rw [show 1 - α = -(α - 1) by ring, div_neg]
    ring
  have hnear : ‖∫ r in Ioc 0 d, F r x - F r y‖ ≤ 2 * A * (d ^ α / α) := by
    have hb : ∀ᵐ r ∂volume.restrict (Ioc 0 d),
        ‖F r x - F r y‖ ≤ 2 * A * r ^ (α - 1) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
      calc
        _ ≤ ‖F r x‖ + ‖F r y‖ := norm_sub_le _ _
        _ ≤ A * r ^ (α - 1) + A * r ^ (α - 1) := add_le_add (hsize r hr.1 x) (hsize r hr.1 y)
        _ = _ := by ring
    have hh := norm_integral_le_of_norm_le (hni.const_mul (2 * A)) hb
    rwa [integral_const_mul, hnint] at hh
  have hfar : ‖∫ r in Ioi d, F r x - F r y‖ ≤ B * d * (d ^ (α - 1) / (1 - α)) := by
    have hb : ∀ᵐ r ∂volume.restrict (Ioi d),
        ‖F r x - F r y‖ ≤ (B * d) * r ^ (α - 2) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      exact (hlip r (hd.trans hr) x y).trans_eq (by dsimp [d]; ring)
    have hh := norm_integral_le_of_norm_le (hfi.const_mul (B * d)) hb
    rwa [integral_const_mul, hfint] at hh
  have hdiff := (hi x).sub (hi y)
  have hsplit : (∫ r in Ioi 0, F r x - F r y) =
      (∫ r in Ioc 0 d, F r x - F r y) + ∫ r in Ioi d, F r x - F r y := by
    rw [← Ioc_union_Ioi_eq_Ioi hd.le]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hdiff.mono_set Ioc_subset_Ioi_self) (hdiff.mono_set (Ioi_subset_Ioi hd.le))
  rw [← integral_sub (hi x) (hi y), hsplit]
  calc
    _ ≤ ‖∫ r in Ioc 0 d, F r x - F r y‖ + ‖∫ r in Ioi d, F r x - F r y‖ := norm_add_le _ _
    _ ≤ 2 * A * (d ^ α / α) + B * d * (d ^ (α - 1) / (1 - α)) := add_le_add hnear hfar
    _ = _ := by
      change _ = (2 * A / α + B / (1 - α)) * d ^ α
      rw [Real.rpow_sub hd, Real.rpow_one]
      field_simp
      <;> ring

theorem bounded_scale_integral_holder {X Y : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {F : ℝ → X → Y} {α A B : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hi : ∀ x, IntegrableOn (fun r => F r x) (Ioc 0 1) volume)
    (hsize : ∀ r ∈ Ioc (0 : ℝ) 1, ∀ x, ‖F r x‖ ≤ A * r ^ (α - 1))
    (hlip : ∀ r ∈ Ioc (0 : ℝ) 1, ∀ x y, ‖F r x - F r y‖ ≤ B * r ^ (α - 2) * ‖x - y‖)
    (x y : X) :
    ‖(∫ r in Ioc 0 1, F r x) - ∫ r in Ioc 0 1, F r y‖ ≤
      (2 * A / α + B / (1 - α)) * ‖x - y‖ ^ α := by
  let G : ℝ → X → Y := fun r x => (Ioc (0 : ℝ) 1).indicator (fun r => F r x) r
  have hset : Ioc (0 : ℝ) 1 ∩ Ioi 0 = Ioc 0 1 := inter_eq_left.mpr Ioc_subset_Ioi_self
  have hgi (x : X) : IntegrableOn (fun r => G r x) (Ioi 0) volume := by
    apply (integrable_indicator_iff measurableSet_Ioc).mpr
    simpa only [IntegrableOn, Measure.restrict_restrict measurableSet_Ioc, hset] using hi x
  have hge (x : X) : (∫ r in Ioi 0, G r x) = ∫ r in Ioc 0 1, F r x := by
    dsimp only [G]
    rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc, hset]
  have hgs (r : ℝ) (hr : 0 < r) (x : X) : ‖G r x‖ ≤ A * r ^ (α - 1) := by
    by_cases hs : r ∈ Ioc (0 : ℝ) 1
    · simpa only [G, indicator_of_mem hs] using hsize r hs x
    · simp only [G, indicator_of_notMem hs, norm_zero]
      exact mul_nonneg hA (Real.rpow_nonneg hr.le _)
  have hgl (r : ℝ) (hr : 0 < r) (x y : X) :
      ‖G r x - G r y‖ ≤ B * r ^ (α - 2) * ‖x - y‖ := by
    by_cases hs : r ∈ Ioc (0 : ℝ) 1
    · simpa only [G, indicator_of_mem hs] using hlip r hs x y
    · simp only [G, indicator_of_notMem hs, sub_self, norm_zero]
      exact mul_nonneg (mul_nonneg hB (Real.rpow_nonneg hr.le _)) (norm_nonneg _)
  simpa only [hge] using scale_integral_holder hα hα1 hA hB hgi hgs hgl x y

end Submission.Obl.Entropy__smooth_gaussian_transport
