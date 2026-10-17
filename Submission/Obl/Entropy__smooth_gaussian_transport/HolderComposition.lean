import Submission.Obl.Entropy__smooth_gaussian_transport.UniformBoundedHolder
import Submission.Obl.Entropy__smooth_gaussian_transport.SegmentMean

open Set

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem UniformBoundedHolder.comp_lipschitz {ι X Y Z : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    {α : ℝ} {f : ι → X → Y} (hf : UniformBoundedHolder α f)
    {P : Y → Z} {L : NNReal} (hP : LipschitzWith L P) :
    UniformBoundedHolder α (fun i x => P (f i x)) := by
  obtain ⟨M, C, hM, hC, hb, hm⟩ := hf
  refine ⟨L * M + ‖P 0‖, L * C, by positivity, by positivity, ?_, ?_⟩
  · intro i x
    calc
      ‖P (f i x)‖ ≤ ‖P (f i x) - P 0‖ + ‖P 0‖ := norm_le_norm_sub_add _ _
      _ ≤ L * ‖f i x‖ + ‖P 0‖ := by gcongr; simpa only [dist_eq_norm, sub_zero] using hP.dist_le_mul (f i x) 0
      _ ≤ _ := by gcongr; exact hb i x
  · intro i x y
    calc
      _ ≤ L * ‖f i x - f i y‖ := by simpa only [dist_eq_norm] using hP.dist_le_mul (f i x) (f i y)
      _ ≤ L * (C * ‖x - y‖ ^ α) := by gcongr; exact hm i x y
      _ = _ := by ring

theorem UniformBoundedHolder.translate {ι X Y : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {α : ℝ} {f : ι → X → Y} (hf : UniformBoundedHolder α f) (a : ι → X) :
    UniformBoundedHolder α (fun i x => f i (x + a i)) := by
  obtain ⟨M, C, hM, hC, hb, hm⟩ := hf
  exact ⟨M, C, hM, hC, fun i x => hb i _, fun i x y => by
    simpa only [add_sub_add_right_eq_sub] using hm i (x + a i) (y + a i)⟩

theorem UniformBoundedHolder.segmentMean {ι X Y Z : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    {α : ℝ} {a b : ι → X → Y}
    (ha : UniformBoundedHolder α a) (hb : UniformBoundedHolder α b)
    {P : Y → Z} {L : NNReal} (hP : LipschitzWith L P) :
    UniformBoundedHolder α (fun i x => segmentMean P (a i x) (b i x)) := by
  obtain ⟨M, C, hM, hC, hba, hma⟩ := ha
  obtain ⟨N, D, hN, hD, hbb, hmb⟩ := hb
  refine ⟨L * max M N + ‖P 0‖, L * max C D, by positivity, by positivity, ?_, ?_⟩
  · intro i x
    have hh := segmentMean_lipschitz (convex_univ : Convex ℝ (univ : Set Y)) hP.lipschitzOnWith
      (mem_univ (a i x)) (mem_univ (b i x)) (mem_univ (0 : Y)) (mem_univ (0 : Y))
    rw [segmentMean_self] at hh
    simp only [sub_zero] at hh
    calc
      _ ≤ ‖Submission.Obl.Entropy__smooth_gaussian_transport.segmentMean P (a i x) (b i x) - P 0‖ + ‖P 0‖ := norm_le_norm_sub_add _ (P 0)
      _ ≤ L * max ‖a i x‖ ‖b i x‖ + ‖P 0‖ := add_le_add hh le_rfl
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (max_le_max (hba i x) (hbb i x)) L.coe_nonneg) le_rfl
  · intro i x y
    have hh := segmentMean_lipschitz (convex_univ : Convex ℝ (univ : Set Y)) hP.lipschitzOnWith
      (mem_univ (a i x)) (mem_univ (b i x)) (mem_univ (a i y)) (mem_univ (b i y))
    calc
      _ ≤ L * max ‖a i x - a i y‖ ‖b i x - b i y‖ := hh
      _ ≤ L * max (C * ‖x - y‖ ^ α) (D * ‖x - y‖ ^ α) := by
        gcongr; exact hma i x y; exact hmb i x y
      _ ≤ L * ((max C D) * ‖x - y‖ ^ α) := by
        apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
        exact max_le (mul_le_mul_of_nonneg_right (le_max_left C D) (Real.rpow_nonneg (norm_nonneg _) _))
          (mul_le_mul_of_nonneg_right (le_max_right C D) (Real.rpow_nonneg (norm_nonneg _) _))
      _ = _ := by ring

end Submission.Obl.Entropy__smooth_gaussian_transport
