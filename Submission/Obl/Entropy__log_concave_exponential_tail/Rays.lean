import Mathlib

open MeasureTheory Set Metric

namespace Submission.Obl.Entropy__log_concave_exponential_tail

/-- A bounded positive superlevel and upper semicontinuity turn log-concavity
into a pointwise exponential bound. -/
theorem exponential_bound_of_bounded_superlevel {m : ℕ}
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hfuc : UpperSemicontinuous f)
    (hfconc : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    {t : ℝ} {c : EuclideanSpace ℝ (Fin m)} (ht : 0 < t) (hc : t < f c)
    (hbound : Bornology.IsBounded {x | t ≤ f x}) :
    ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧ ∀ x, f x ≤ Real.exp (b - a * ‖x‖) := by
  obtain ⟨R, hR, hlevel⟩ := hbound.subset_ball_lt 0 c
  have hcpos : 0 < f c := ht.trans hc
  let a : ℝ := (Real.log (f c) - Real.log t) / R
  have ha : 0 < a := div_pos (sub_pos.mpr (Real.log_lt_log ht hc)) hR
  obtain ⟨M, hM⟩ := UpperSemicontinuousOn.bddAbove_of_isCompact
    (isCompact_closedBall c R) (hfuc.upperSemicontinuousOn (closedBall c R))
  let b : ℝ := max 0 (max (Real.log (f c) + a * ‖c‖) (M + a * (R + ‖c‖)))
  have hb0 : 0 ≤ b := le_max_left _ _
  have hbc : Real.log (f c) + a * ‖c‖ ≤ b :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hbM : M + a * (R + ‖c‖) ≤ b :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨a, b, ha, hb0, ?_⟩
  intro x
  by_cases hxpos : 0 < f x
  swap
  · exact (le_of_not_gt hxpos).trans (Real.exp_pos _).le
  by_cases hxR : ‖x - c‖ ≤ R
  · have hxball : x ∈ closedBall c R := by simpa only [mem_closedBall, dist_eq_norm] using hxR
    have hfx : f x ≤ M := hM (mem_image_of_mem f hxball)
    have hxnorm : ‖x‖ ≤ R + ‖c‖ := (norm_le_norm_sub_add x c).trans (by linarith)
    have hMexp : M ≤ b - a * ‖x‖ := by
      have := mul_le_mul_of_nonneg_left hxnorm ha.le
      linarith
    have hMself : M ≤ Real.exp M := by linarith [Real.add_one_le_exp M]
    exact hfx.trans (hMself.trans (Real.exp_le_exp.mpr hMexp))
  have hd : 0 < ‖x - c‖ := hR.trans (lt_of_not_ge hxR)
  let q : ℝ := R / ‖x - c‖
  have hqpos : 0 < q := div_pos hR hd
  have hqle : q ≤ 1 := (div_le_one hd).mpr (le_of_not_ge hxR)
  have hqmul : q * ‖x - c‖ = R := div_mul_cancel₀ _ hd.ne'
  let z : EuclideanSpace ℝ (Fin m) := (1 - q) • c + q • x
  have hzpos : 0 < f z := hfconc.1 hcpos hxpos (sub_nonneg.mpr hqle) hqpos.le (by ring)
  have hzsub : z - c = q • (x - c) := by dsimp [z]; module
  have hznorm : ‖z - c‖ = R := by
    rw [hzsub, norm_smul, Real.norm_of_nonneg hqpos.le, hqmul]
  have hzlt : f z < t := by
    by_contra! hz
    have := hlevel hz
    rw [mem_ball, dist_eq_norm, hznorm] at this
    exact lt_irrefl _ this
  have hconc : (1 - q) * Real.log (f c) + q * Real.log (f x) ≤ Real.log (f z) := by
    simpa only [smul_eq_mul] using
      hfconc.2 hcpos hxpos (sub_nonneg.mpr hqle) hqpos.le (by ring)
  have hlog : (1 - q) * Real.log (f c) + q * Real.log (f x) ≤ Real.log t :=
    hconc.trans (Real.log_lt_log hzpos hzlt).le
  have hscaled : (‖x - c‖ - R) * Real.log (f c) + R * Real.log (f x) ≤
      ‖x - c‖ * Real.log t := by
    calc
      _ = ‖x - c‖ * ((1 - q) * Real.log (f c) + q * Real.log (f x)) := by
        dsimp [q]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog hd.le
  have htail : Real.log (f x) ≤ Real.log (f c) - a * ‖x - c‖ := by
    apply (mul_le_mul_iff_right₀ hR).mp
    calc
      R * Real.log (f x) ≤ Real.log (f c) * R -
          (Real.log (f c) - Real.log t) * ‖x - c‖ := by nlinarith [hscaled]
      _ = R * (Real.log (f c) - a * ‖x - c‖) := by
        dsimp [a]
        field_simp
  apply (Real.log_le_iff_le_exp hxpos).mp
  have hnorm := mul_le_mul_of_nonneg_left (norm_sub_norm_le x c) ha.le
  linarith

end Submission.Obl.Entropy__log_concave_exponential_tail
