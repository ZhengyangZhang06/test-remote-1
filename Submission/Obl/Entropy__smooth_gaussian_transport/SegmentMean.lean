import Submission.Obl.Entropy__smooth_gaussian_transport.DirectionalQuotient

open MeasureTheory Set

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def segmentMean {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (P : X → Y) (a b : X) : Y :=
  ∫ t in (0 : ℝ)..1, P ((1 - t) • a + t • b)

theorem segmentMean_self {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] (P : X → Y) (a : X) :
    segmentMean P a a = P a := by
  have he (t : ℝ) : (1 - t) • a + t • a = a := by module
  simp only [segmentMean, he, intervalIntegral.integral_const, sub_zero, one_smul]

theorem convex_combination_sub_norm_le {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] (a b c d : X) {t : ℝ} (ht : t ∈ Icc 0 1) :
    ‖((1 - t) • a + t • b) - ((1 - t) • c + t • d)‖ ≤ max ‖a - c‖ ‖b - d‖ := by
  have he : ((1 - t) • a + t • b) - ((1 - t) • c + t • d) =
      (1 - t) • (a - c) + t • (b - d) := by module
  rw [he]
  calc
    _ ≤ ‖(1 - t) • (a - c)‖ + ‖t • (b - d)‖ := norm_add_le _ _
    _ = (1 - t) * ‖a - c‖ + t * ‖b - d‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
    _ ≤ (1 - t) * max ‖a - c‖ ‖b - d‖ + t * max ‖a - c‖ ‖b - d‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left (le_max_right _ _) ht.1)
    _ = _ := by ring

theorem segmentMean_lipschitz {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {P : X → Y} {S : Set X} {L : NNReal} (hS : Convex ℝ S) (hP : LipschitzOnWith L P S)
    {a b c d : X} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) :
    ‖segmentMean P a b - segmentMean P c d‖ ≤ (L : ℝ) * max ‖a - c‖ ‖b - d‖ := by
  have hmem {u w : X} (hu : u ∈ S) (hw : w ∈ S) {t : ℝ} (ht : t ∈ Icc 0 1) :
      (1 - t) • u + t • w ∈ S :=
    hS hu hw (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hcont {u w : X} (hu : u ∈ S) (hw : w ∈ S) :
      ContinuousOn (fun t : ℝ => P ((1 - t) • u + t • w)) (Icc 0 1) :=
    hP.continuousOn.comp (by fun_prop) (fun t ht => hmem hu hw ht)
  rw [segmentMean, segmentMean, ← intervalIntegral.integral_sub
    ((hcont ha hb).intervalIntegrable_of_Icc (by norm_num))
    ((hcont hc hd).intervalIntegrable_of_Icc (by norm_num))]
  apply interval_average_norm_bound
  intro t ht
  calc
    _ ≤ (L : ℝ) * ‖((1 - t) • a + t • b) - ((1 - t) • c + t • d)‖ := by
      simpa only [dist_eq_norm] using hP.dist_le_mul _ (hmem ha hb ht) _ (hmem hc hd ht)
    _ ≤ _ := mul_le_mul_of_nonneg_left (convex_combination_sub_norm_le a b c d ht) L.coe_nonneg

end Submission.Obl.Entropy__smooth_gaussian_transport
