import Mathlib

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.Entropy__log_concave_exponential_tail

/-- A measurable convex set of positive finite volume is bounded. -/
theorem convex_isBounded_of_volume {m : ℕ} {s : Set (EuclideanSpace ℝ (Fin m))}
    (hs : Convex ℝ s) (hsm : MeasurableSet s)
    (hspos : 0 < volume s) (hsfin : volume s < ∞) : Bornology.IsBounded s := by
  obtain ⟨K, hKs, hK, hKpos⟩ := hsm.exists_lt_isCompact hspos
  let ε : ℝ≥0∞ := ENNReal.ofReal (|(1 / 2 : ℝ) ^ Module.finrank ℝ
    (EuclideanSpace ℝ (Fin m))|) * volume K
  have hε : ε ≠ 0 := by
    dsimp [ε]
    positivity
  obtain ⟨L, hLs, hL, hLsmall⟩ := hsm.exists_isCompact_sdiff_lt hsfin.ne hε
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨T, hT⟩ := hL.isBounded.exists_norm_le
  refine isBounded_iff_forall_norm_le.mpr ⟨2 * T + R, ?_⟩
  intro x hx
  have hmid (y : EuclideanSpace ℝ (Fin m)) :
      AffineMap.homothety x (1 / 2 : ℝ) y = (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y := by
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    module
  have hmass : volume (AffineMap.homothety x (1 / 2 : ℝ) '' K) = ε := by
    exact Measure.addHaar_image_homothety volume x (1 / 2 : ℝ) K
  have hinter : ∃ y ∈ K, AffineMap.homothety x (1 / 2 : ℝ) y ∈ L := by
    by_contra! h
    have hsub : AffineMap.homothety x (1 / 2 : ℝ) '' K ⊆ s \ L := by
      rintro z ⟨y, hy, rfl⟩
      refine ⟨?_, h y hy⟩
      rw [hmid]
      exact hs hx (hKs hy) (by norm_num) (by norm_num) (by norm_num)
    have := (measure_mono hsub).trans_lt hLsmall
    rw [hmass] at this
    exact lt_irrefl _ this
  obtain ⟨y, hy, hz⟩ := hinter
  have hxid : x = (2 : ℝ) • AffineMap.homothety x (1 / 2 : ℝ) y - y := by
    rw [hmid]
    module
  calc
    ‖x‖ = ‖(2 : ℝ) • AffineMap.homothety x (1 / 2 : ℝ) y - y‖ := congrArg norm hxid
    _ ≤ ‖(2 : ℝ) • AffineMap.homothety x (1 / 2 : ℝ) y‖ + ‖y‖ := norm_sub_le _ _
    _ = 2 * ‖AffineMap.homothety x (1 / 2 : ℝ) y‖ + ‖y‖ := by
      rw [norm_smul]
      norm_num
    _ ≤ 2 * T + R := by gcongr <;> [exact hT _ hz; exact hR _ hy]

end Submission.Obl.Entropy__log_concave_exponential_tail
